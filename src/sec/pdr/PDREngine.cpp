// Copyright 2024-2026 keplertech.io
// SPDX-License-Identifier: GPL-3.0-only

#include "pdr/PDREngine.h"

#include <algorithm>
#include <cstdlib>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#if defined(__APPLE__)
#include <malloc/malloc.h>
#elif defined(__GLIBC__)
#include <malloc.h>
#endif

#include "common/BoolExprUtils.h"
#include "common/ProofProblemDebug.h"
#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "proof/ProofEngineShared.h"
#include "proof/TransitionExprResolver.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

namespace detail {

bool pdrStateEqualitySubsetPrefersCadical(
    bool usesDualRailStateEncoding,
    size_t equalityPairCount,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t solverSymbols,
    size_t pairLimit,
    size_t symbolLimit) {
  return usesDualRailStateEncoding &&
         solverType == KEPLER_FORMAL::Config::SolverType::KISSAT &&
         (equalityPairCount >= pairLimit || solverSymbols >= symbolLimit);
}

bool pdrResetBootstrapPrecheckTooLarge(bool usesDualRailStateEncoding,
                                       size_t observedOutputCount,
                                       size_t originalObservedOutputCount,
                                       size_t transitionSources,
                                       size_t transitionSourceLimit,
                                       size_t outputLimit) {
  if (!usesDualRailStateEncoding) {
    return false;
  }
  const size_t fullOutputSurface =
      std::max(observedOutputCount, originalObservedOutputCount);
  return transitionSources > transitionSourceLimit ||
         fullOutputSurface > outputLimit;
}

std::vector<size_t> makeDeterministicPdrWorklist(
    const std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
  std::sort(worklist.begin(), worklist.end());
  return worklist;
}

std::vector<size_t> makePdrClosureWorklist(
    const std::unordered_set<size_t>& symbols) {
  // Partner closure has no cap, and every caller sorts the final symbol vector
  // before SAT encoding. Avoid sorting this temporary worklist on wide
  // dual-rail leaves; traversal order cannot change the closed symbol set.
  return std::vector<size_t>(symbols.begin(), symbols.end());
}

bool pdrCubeLiteralOrderLess(size_t lhsSymbol,
                             bool lhsValue,
                             size_t rhsSymbol,
                             bool rhsValue) {
  if (lhsSymbol != rhsSymbol) {
    return lhsSymbol < rhsSymbol;
  }
  return lhsValue < rhsValue;
}

bool pdrCubeAssignmentOrderLess(
    const std::vector<std::pair<size_t, bool>>& lhs,
    const std::vector<std::pair<size_t, bool>>& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), [](const auto& a,
                                                         const auto& b) {
        return pdrCubeLiteralOrderLess(a.first, a.second, b.first, b.second);
      });
}

}  // namespace detail

// Overall PDR algorithm:
// 1. Build Init from the SEC startup constraints and reuse any already
//    validated strengthening invariant when it is sound to do so.
// 2. Maintain frames F[0], F[1], ... where each frame stores clauses known to
//    hold for all states reachable within that many steps.
// 3. At each level, ask whether a bad state still survives the current frame.
// 4. If so, recursively search for predecessors until either Init is reached
//    (real counterexample) or the bad cube is blocked by a learned clause.
// 5. Generalize learned blocking clauses, add them to all earlier frames, and
//    then propagate them forward when the transition relation preserves them.
// 6. Stop once two adjacent frames converge, when a real bug is found, or when
//    the requested frame budget is exhausted.

namespace {

// The init-intersection fast path runs inside literal-dropping generalization.
// On ASICs the complemented-state table can be enormous while each cube is
// tiny, so scanning the full table per literal costs more than the SAT queries
// it was meant to avoid. Above this limit we skip only the cheap contradiction
// shortcut and conservatively treat the cube as init-intersecting below.
constexpr size_t kMaxComplementPairsForCheapInitCheck = 1024;
// Reset-constant evaluation is only a shortcut before the exact reset-image
// SAT check. Bound the recursive evaluator so an ASIC memory cone cannot spend
// minutes proving that the shortcut is inconclusive.
constexpr size_t kMaxResetConstantEvaluatorStates = 1024;
constexpr size_t kMaxResetConstantEvaluatorExprs = 8192;
// BlackParrot samples showed the remaining exact-base fallback came from
// reset-specialized misses before support was even collected. Allow the
// symbolic reset image to traverse that local cone; the SAT proof below is
// still separately capped, so larger traversal does not admit broad CDCL work.
constexpr size_t kMaxResetSymbolicEvaluatorStates = 131072;
constexpr size_t kMaxResetSymbolicEvaluatorExprs = 1048576;
// Reset-specialized symbolic evaluation substitutes reset controls and startup
// facts into transition cones. Sampling BlackParrot showed the evaluator still
// walking huge reset-mux data branches before BoolExpr::And/Or could fold the
// controlling reset literal. Do a tiny allocation-free probe first so obvious
// reset-gated constants short-circuit before the full recursive expansion.
constexpr size_t kMaxResetSymbolicCheapEvalNodes = 1024;
// BlackParrot sampling showed deep concrete validation repeatedly disproving
// tiny reset cores, then falling into the exact reset-frontier BMC builder only
// because the symbolic reset-image traversal hit its generic shortcut budget at
// target_step=7.  Keep the larger budget restricted to small root cubes: the
// later SAT proof is still independently support/resource capped.
constexpr size_t kMaxDeepSmallCubeResetSymbolicEvaluatorStates = 1048576;
constexpr size_t kMaxDeepSmallCubeResetSymbolicEvaluatorExprs = 8388608;
constexpr size_t kMaxDeepSmallCubeResetSymbolicLiterals = 4;
// BlackParrot dual-rail PDR can rediscover a small reset-frontier root at the
// next concrete reset frame.  Revalidating those few literals through the
// reset-specialized evaluator is far smaller than opening the 600k-symbol
// reset-frontier BMC, but the generic small-cube traversal cap is too low for
// the deep dual-rail cone. Keep the larger budget restricted to small cubes on
// large dual-rail surfaces.
constexpr size_t kMaxDeepLargeDualRailResetSymbolicEvaluatorStates =
    4194304;
constexpr size_t kMaxDeepLargeDualRailResetSymbolicEvaluatorExprs =
    33554432;
// A fresh exact reset-frontier query materializes the reset-prefix BMC over the
// whole large dual-rail surface.  BlackParrot final PDR already reaches ~9GiB
// when doing this at post-bootstrap step 3 and spikes above 10GiB at step 4.
// Keep the exact proof available for the shallower frames that seed reusable
// reset cores, then stop through the normal PDR budget path instead of opening
// another one-shot SAT context.
constexpr size_t kMaxFreshLargeDualRailExactResetFrontierPostBootstrapStep = 3;
constexpr size_t kMaxFreshLargeDualRailSingletonResetFrontierPostBootstrapStep =
    kMaxFreshLargeDualRailExactResetFrontierPostBootstrapStep;
// Deep reset repair only needs this as a shortcut.  Sampling showed
// target_step=6 spending seconds recursively canonicalizing huge reset cones
// that were later rejected by the local support cap.  Bound the walk and fall
// back to ordinary PDR when the shortcut stops being local.
constexpr size_t kMaxDeepResetExpressionCanonicalizeNodes = 8192;
// AES PDR samples produced reset-unreachable root cubes with 108 literals.
// They were too wide for the old toy cap and fell back to the exact
// reset-frontier assumption query, which dominated runtime. The
// expression shortcut is still guarded by support/expansion caps below; this
// cube cap only prevents pathologically huge clauses from being tried.
constexpr size_t kMaxResetSpecializedExpressionCube = 128;
// BlackParrot reset leaves measured supports just above the old caps
// (4097/4421, then 8193/9251 after deeper reset-core reuse). Keep this below
// general ASIC scale, but wide enough for the measured local bootstrap relation
// so the reset-expression proof can avoid the much larger reset-summary query.
constexpr size_t kMaxResetSpecializedExpressionSupport = 16384;
constexpr size_t kMaxResetSpecializedExpressionPairProbeCube = 8;
constexpr size_t kMaxResetSpecializedExpressionPairProbes = 4;
constexpr size_t kMaxResetSpecializedExpressionTripleProbes = 8;
// The bootstrap-expression rewriter is an optional congruence shortcut after
// direct equality-index checks. BlackParrot samples showed 124 bootstrap
// equalities spending the whole run recursively rewriting large expressions
// before any SAT/PDR work could proceed. Keep the quotient for local cases and
// skip it for ASIC-sized equality sets; missing this shortcut is conservative.
constexpr size_t kMaxBootstrapExpressionRewritePairs = 64;
constexpr size_t kMaxBootstrapExpressionRewriteNodes = 8192;
// Keep reset-expression SAT as a local proof shortcut. AES samples showed
// support-129/135 pair proofs closing quickly, while support-274+ proofs spent
// their time in CDCL before falling through to exact reset validation anyway.
// Pair/triple probes and the full-cube fallback therefore share the same local
// cap instead of admitting broad small-cube SAT queries.
constexpr size_t kMaxResetSpecializedExpressionPairProbeSupport = 256;
constexpr size_t kMaxResetSpecializedExpressionTripleProbeSupport = 256;
constexpr size_t kMaxResetSpecializedExpressionFullSatSupport = 256;
constexpr size_t kMaxResetSpecializedExpressionSmallCubeFullSatSupport = 256;
// The reset-expression SAT fallback is only a shortcut after the cached
// canonical/bootstrap-rewrite checks. BlackParrot samples showed this fallback
// rebuilding a broad equality rewriter per cube; if the selected equality set
// is not local, skip the shortcut instead of making optional rewriting the
// proof wall.
constexpr size_t kMaxResetExpressionProofRewriteEqualities = 32;
// Reset-expression SAT is an optional PDR shortcut. Sampling showed some
// support-500-ish local proofs spending minutes in CDCL; cap each proof and
// let UNKNOWN fall through to the exact reset-validation path.
constexpr unsigned kDefaultResetExpressionProofConflictLimit = 50000;
// Node counts are reserve hints only. Sampled reset-frontier queries spent all
// CPU counting tens of thousands of transition DAGs before encoding them. Use
// exact hints for local groups and rely on the encoder's bounded growth for
// ASIC-sized groups.
constexpr size_t kMaxExactTransitionNodeCountHintTargets = 512;
// Reset-frontier concrete validation may consume the already-proved PDR frame
// invariant as an exact reachable-state fact. Keep that extra BMC constraint
// local; broad invariants can otherwise pull the final candidate check back
// toward a whole-chip unroll.
constexpr size_t kMaxResetReachabilityFrameInvariantSupport = 64;
// Shallow reset-frontier validation benefits from the per-frame caches and
// reset-specialized shortcuts. BlackParrot sampling showed deep projected
// traces rebuilding/solving a wide exact query once per frame, even in cached
// assumption mode. At that point the exact shared-prefix checker is cheaper
// and still proves the same concrete bounded-reachability question.
constexpr size_t kSharedPrefixConcreteValidationMinDepth = 3;
// Keep one-shot per-frame checking only for the startup and first post-reset
// frames. BlackParrot frame-2 samples showed repeated six-literal roots
// rebuilding the same reset-frontier solver; cached assumptions reuse that
// support solver while proving the same concrete reachability query.
constexpr size_t kMaxPerFrameConcreteValidationDepth = 1;
constexpr size_t kMaxPerFrameConcreteValidationCubeLiterals = 8;
// One-shot concrete root validation is good for shallow checks because the
// cube is encoded directly as unit clauses.  BlackParrot sampling showed deeper
// projected traces rebuilding the same 90k+ symbol reset-prefix solver for
// neighboring six-literal cubes; use the cached-assumption checker for that
// measured deeper/wider shape so exact queries can reuse solvers and failed
// cores, while tiny two-literal projected checks keep the cheaper one-shot
// path covered by focused unit tests.
constexpr size_t kCachedConcreteValidationMinDepth = 2;
constexpr size_t kCachedConcreteValidationMinCubeLiterals = 3;
// Large dual-rail final PDR slices can reach abstract reset-frontier roots
// whose concrete validation needs a huge reset-prefix solver. BlackParrot final
// reproduces this with four-literal roots on a 2.6M-rail surface. Once exact
// reset-frontier repair is already disabled by the global rail-size guard, do
// not let those projected roots rebuild that solver anyway; split/skip through
// the caller's existing inconclusive path instead.
constexpr size_t kMinLargeDualRailRootForConcreteValidationSkip = 4;
// Swerv is above the broad exact-reset-frontier rail limit, but its isolated
// final leaves are still small enough for local concrete root repair. Keep
// BP-scale surfaces behind the skip above.
constexpr size_t kMaxLocalDualRailFinalLeafRepairStateSymbols = 128 * 1024;
constexpr size_t kMaxLocalDualRailFinalLeafRepairRootLiterals = 32;
// Strategy-level caps use the original output count to protect BP-sized runs.
// Local Swerv leaves have a much smaller rail-state surface after output
// splitting, so keep their exact repair bounded but not BP-tight.
constexpr size_t kMinLocalDualRailFinalLeafPredecessorSupport = 16 * 1024;
constexpr size_t kMinLocalDualRailFinalLeafPredecessorProjection = 32;
constexpr size_t kMinLocalDualRailFinalLeafPredecessorQueries = 8192;
constexpr size_t kMinLocalDualRailFinalLeafProjectedRefinements = 32;
// If cheap reset facts already prove all but a couple of concrete root
// validation frames, do not open the broad shared-prefix assumption solver.
// Sampled BlackParrot leaves got stuck in assumption solving on that shape; exact
// per-frame unit-clause queries keep the remaining proof local.
constexpr size_t kMaxSparseConcreteReachabilityPerFrameChecks = 2;
// Final multi-output SEC batches should not spend minutes repairing or
// validating deeper projected roots through the concrete reset prefix.
// Returning the candidate at that point is conservative: the SEC strategy
// splits the output batch and retries with the same PDR proof rules on smaller
// properties, while single-output leaves still require concrete validation
// before reporting a real difference. BlackParrot samples showed the frame-2/3
// two-output repairs dominating runtime after the frame-1 clauses were learned.
constexpr size_t kMaxMultiOutputProjectedRootValidationFrame = 1;
// Bounded root-cube generalization is optional clause strengthening after a
// projected counterexample was already disproved by exact concrete
// reachability. On BlackParrot, once validation reaches the shared-prefix
// reset checker, each literal drop opens another expensive bounded proof.
// Learn the already-disproved root cube verbatim at those depths.
constexpr size_t kMaxDepthForBoundedRootGeneralization = 2;
constexpr size_t kMinStateSymbolsForDeepRootGeneralizationBypass = 512;
// The first bad obligation controls how much abstraction PDR is allowed to use.
// A tiny structural justification can be too weak on large SEC cones and may
// produce an abstract counterexample that concrete BMC later rejects. Prefer a
// full state-support cube when the bad cone is bounded, but keep the structural
// fallback for very large datapaths so one output cannot materialize the whole
// ASIC into every predecessor query.
constexpr size_t kMaxPreciseBadCubeSupportNodes = 262144;
// After exact BMC rejects an abstract final-stage PDR counterexample, a small
// state-only bad predicate can be turned into frame clauses directly. Keep the
// enumeration deliberately small: this is for one-output ASIC cones such as
// BlackParrot's six-state-bit bad predicates, not arbitrary datapath CNF.
constexpr size_t kMaxValidatedBadFormulaCnfSupport = 8;
constexpr size_t kMaxDualRailValidatedBadFormulaCnfSupport = 12;
// Batched SEC bad predicates are an OR of per-output mismatches. Each output
// may have a small state-only bad cone even when the union across the batch is
// too wide to enumerate. Cap the total learned clauses so the batched
// refinement stays a local PDR repair instead of becoming a broad CNF dump.
constexpr size_t kMaxValidatedBadFormulaClauses = 4096;
// The exact validation query for a broad batch is itself a bounded-model check
// over the OR of all candidate bad clauses. AES samples showed that validating
// a 16-output slice before trying the narrow root-cube CEGAR path can dominate
// runtime. Keep broad bad-formula learning for genuinely small batches; larger
// batches fall back to the existing exact cube validation, which asks only
// about the current projected counterexample.
constexpr size_t kMaxExactValidatedBadFormulaClauses = 8;
// Deep single-output leaves can enumerate to 32 small state clauses. Sampling
// BlackParrot showed the optional whole-bad-formula base proof becoming a
// repeated Kissat wall after reset-specialized validation had already learned
// the useful local clauses. Keep that whole-formula proof for root/small cases
// and let deeper leaves continue through ordinary PDR/root-cube refinement.
constexpr size_t kMaxWholeBadFormulaBaseValidationFrame = 1;
// When exact root-cube validation has already proved that PDR is enumerating
// reset-unreachable assignments of one small output-bad predicate, a shallow
// exact whole-predicate proof can learn the rest of that local CNF. Keep this
// at the startup frontier: BlackParrot sampling showed the frame-3 version
// turning into an unbounded SAT wall instead of an incremental PDR repair.
constexpr size_t kMaxWholeBadFormulaBaseValidationAfterCachedRootFrame = 1;
// Single-output final leaves validate the whole output-bad predicate with one
// bounded-frontier query before learning any clause. BlackParrot sampling
// showed 32-clause, tiny-support predicates otherwise degenerating into tens of
// thousands of neighboring root-cube predecessor checks, so allow that compact
// exact repair without relaxing the multi-output/batched path.
constexpr size_t kMaxSingleOutputExactValidatedBadFormulaClauses = 64;
// Dual-rail output predicates often stay local in logical state but enumerate
// many Boolean rail assignments. Keep the binary SEC cap untouched, and allow
// the wider assignment set only when the problem explicitly uses rail state.
constexpr size_t kMaxDualRailSingleOutputExactValidatedBadFormulaClauses =
    kMaxValidatedBadFormulaClauses;
// Exact reset-frontier checks are a concrete-reachability repair path.  They
// are useful on small and mid-size reset-bootstrap designs, but large dual-rail
// problems rebuild the reset prefix over both value/known rails for many
// neighboring PDR cubes.  Nangate45 Ibex needs this repair at 15496 rail
// symbols/transition sources to avoid abstract reset-frontier counterexamples.
// Sky130HS RISC-V has a 99-output, 4224-rail bus surface where ordinary PDR can
// exhaust bad-cube budgets.  Nangate45 dynamic-node exposes a similar
// medium-wide 331-output reset-frontier surface at roughly 18k rail symbols.
// Keep those medium surfaces eligible for exact repair while leaving larger
// SoC-scale interfaces behind the guards.
constexpr size_t kMaxExactResetFrontierDualRailStateSymbols = 20000;
constexpr size_t kMaxExactResetFrontierDualRailTransitionSources = 20000;
constexpr size_t kMaxExactResetFrontierDualRailMediumOutputs = 384;
constexpr size_t kMaxExactResetFrontierDualRailObservedOutputs =
    kMaxExactResetFrontierDualRailMediumOutputs;
constexpr size_t kMaxExactResetFrontierDualRailSmallOriginalOutputs = 64;
constexpr size_t kMinExactResetFrontierDualRailMediumStateSymbols = 4096;
constexpr size_t kMaxExactResetFrontierDualRailOriginalOutputs =
    kMaxExactResetFrontierDualRailMediumOutputs;
// The broad frame-0 reset-bootstrap BMC precheck materializes the whole output
// slice.  Allow medium CPU interfaces such as 99-output RISC-V, but still keep
// larger SoC-scale surfaces behind the transition/original-output guards.
constexpr size_t kMaxDualRailResetBootstrapBmcTransitionSources = 8192;
constexpr size_t kMaxDualRailResetBootstrapBmcObservedOutputs =
    kMaxExactResetFrontierDualRailMediumOutputs;
constexpr unsigned kDefaultDualRailBadCubeConflictLimit = 20000;
constexpr unsigned kDefaultDualRailPredecessorConflictLimit = 10000;
// Residual one-output leaves need more search than broad batch queries.  Do not
// lower this bound to save runtime; doing so can make a legal PDR obligation
// report inconclusive before the residual repair has had its intended search
// budget.
constexpr unsigned kDefaultDualRailResidualPredecessorConflictLimit = 200000;
constexpr size_t kDefaultDualRailPredecessorEncodingNodeLimit = 1000000;
constexpr size_t kDefaultDualRailPredecessorEncodingSupportLimit = 8192;
constexpr const char* kDualRailPredecessorConflictLimitEnv =
    "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_CONFLICT_LIMIT";
// Exact reset-frontier validation can batch a small state-only bad CNF into
// one prefix query. This replaces many neighboring per-assignment frontier
// solves with a single real bounded proof, and stays limited to local
// output-bad predicates. BlackParrot diagnostics showed frame-2 one-output
// predicates with six state bits otherwise degenerating into hundreds of wide
// predecessor queries. Keep the exact batched proof through that measured
// shallow frame, and leave deeper repair to ordinary PDR/root-cube refinement.
constexpr size_t kMaxResetFrontierBatchedBadFormulaFrame = 2;
constexpr size_t kMaxResetFrontierBatchedBadFormulaSupport = 16;
// Target-frame bad-formula validation is an optional CEGAR repair. Sampling
// BlackParrot showed even a handful of exact target-frame reset-frontier probes
// spending minutes in assumption solving. Keep this repair on the cheap reset/PDR-core
// path; exact projected-counterexample validation remains available outside the
// eager bad-formula loop.
constexpr size_t kMaxPartialTargetResetFrontierBadFormulaFrame = 8;
constexpr size_t kMaxPartialTargetResetFrontierBadFormulaCheapChecks = 64;
constexpr size_t kMaxDualRailPartialTargetResetFrontierBadFormulaCheapChecks =
    512;
constexpr long long kOptionalStartupResetFrontierConflictLimit = 1000;
constexpr long long kOptionalStartupResetFrontierPropagationLimit = 25000;
// Multi-output SEC/PDR batches can still use exact bad-formula repair when the
// repair is decomposed and validated per output. Keep that eager path limited
// to the strategy's small local batches so we do not turn PDR into a broad BMC
// pass over a whole ASIC property.
constexpr size_t kMaxPerOutputValidatedBadFormulaRepairOutputs = 16;
// When the reset-cube validator is available, a broad state-clause batch can
// be checked one clause at a time with a shared reset-frontier context. This
// avoids repeating the same setup once per output group on ASIC regressions.
constexpr size_t kMaxBatchResetCubeValidatedBadFormulaClauses = 2048;
// Exact reset-frontier validation of every state-only bad assignment is useful
// for small local predicates. BlackParrot samples showed 32/64-clause output
// leaves spending their runtime in one hard assumption query after most
// clauses were already handled by reset-specialized conflicts. For larger
// batches, keep the exact cheap conflicts and let ordinary PDR handle the rest.
constexpr size_t kMaxExactResetCubeValidatedBadFormulaClauses = 16;
constexpr size_t kMaxDualRailExactResetCubeValidatedBadFormulaClauses =
    kMaxValidatedBadFormulaClauses;
// Deep single-output bad predicates can still be tiny in state support even
// when they enumerate to more than the broad reset-cube cap above. In that
// measured BlackParrot shape, cache-only repair left 8-22 clauses unvalidated
// and PDR paid for repeated large predecessor queries. Allow an exact
// per-cube reset-frontier repair only while the union support remains local.
constexpr size_t kMaxDeepLocalExactResetCubeValidatedBadFormulaClauses = 64;
// Deep bad-formula reset repair is an optional refinement loop. Sampling on
// BlackParrot showed fresh symbolic reset probes becoming expensive, but later
// stats also showed frame-3 repairs consuming already-proven reset cores one at
// a time. Keep the fresh-probe budget tiny while allowing cached cores to drain
// in one pass.
constexpr size_t kMaxDeepPartialFreshResetConflictClausesPerRepair = 1;
constexpr size_t kMaxDeepCacheOnlyResetConflictClausesPerRepair = 64;
// Non-exact bad-formula repair is a refinement mechanism, not the proof
// itself. Samples showed BlackParrot spending the wall proving all 128
// neighboring reset-unreachable assignments through optional symbolic reset
// rewrites. Stop each visit after a tiny fresh probe seed; exact root
// validation and cached reset cores still supply the real proof obligations.
constexpr size_t kMaxNonExactFreshResetSpecializedProbesPerRepair = 2;
constexpr size_t kMaxBadFormulaRepairResetSymbolicStates = 8192;
constexpr size_t kMaxBadFormulaRepairResetSymbolicExprs = 65536;
// After cheap reset-specialized repair, a few residual state-only bad
// assignments may remain. Keep the exact batch only for shallow local leaves:
// Swerv trace bits need this final exact proof, while deeper BlackParrot
// samples spent the wall in the same optional assumption solve.
constexpr size_t kMaxResidualExactResetCubeValidatedBadFormulaClauses = 32;
constexpr size_t kMaxResidualExactResetCubeValidatedBadFormulaFrame = 1;
constexpr long long kResidualResetFrontierBatchConflictLimit = 1000;
constexpr long long kResidualResetFrontierBatchPropagationLimit = 25000;
// Re-proving prior reset cores at deeper bad frames recursively expands the
// reset image to that target step. Keep it bounded to measured local
// BlackParrot shapes: frame 3/4 was blocked by exact root-validation SAT, and
// frame 12 fell into repeated predecessor transition encoding after the
// cache-only repair skipped every clause. The reset-specialized symbolic proof
// consumes these tiny cores without opening another broad assumption solve.
// Beyond this frame, repair stays cache-only.
constexpr size_t kMaxFreshDeepResetSpecializedBadFormulaRepairFrame = 12;
// The reset-specialized expression shortcut is excellent at the startup
// frontier, but its symbolic unroll grows with the target frame. BlackParrot
// samples at frame 11 spent all CPU/memory recursively constructing reset
// images for the same small bad-formula clauses. Past this frame, bad-formula
// repair only consumes already-proved reset cores; ordinary concrete root
// validation remains responsible for opening new exact reset-image queries.
constexpr size_t kMaxResetSpecializedBadFormulaValidationFrame = 2;
// Priming the reset-frontier cache with the union of a whole validated-clause
// batch is useful only while that union is local. BlackParrot batch-16 samples
// showed the broad prime itself building a 100k+ symbol reset solver before
// most clauses were discharged by cheaper reset-expression conflicts. For
// wider unions, build exact reset-frontier solvers lazily for the few cubes
// that actually need them.
constexpr size_t kMaxResetCubeValidationPrimeSupport = 16;
// Eager bad-formula validation is a useful shortcut on toy and medium control
// problems, but sampled AES PDR runs showed deeper-frontier eager validation
// becoming a standalone BMC wall. Keep deeper eager validation only while the
// state surface is small; large ASIC slices still validate concrete projected
// traces exactly, but ordinary PDR blocking gets the first chance to refine.
constexpr size_t kMaxDeepEagerBadFormulaStateSymbols = 64;
// The DAG walk budget above prevents pathological formula traversal, while
// this state-symbol budget keeps a "bounded" cone from still producing a giant
// target cube. PDR can safely use the structural justification fallback for
// larger cones and any reported counterexample is still concrete-BMC checked.
// A SAT predecessor assignment can mention every state bit in a large target
// transition cone. Carrying that entire model forward makes the next PDR query
// encode hundreds of unrelated next-state functions. The engine therefore has
// a configurable projection limit: above it, keep the SAT query exact but carry
// forward only a bounded set of state literals from the satisfying model.
// Learned clauses are still checked by real predecessor queries before being
// added.
constexpr size_t kMinPredecessorJustificationVisits = 4096;
constexpr size_t kPredecessorJustificationVisitMultiplier = 64;
// Literal-dropping only improves clause strength; it is not required for
// soundness.  ASIC predecessor cubes can still contain hundreds of literals,
// and learning them almost verbatim makes PDR rediscover nearby cubes.  Use a
// bounded chunk-dropping pass: each proposed stronger clause is validated by
// the same predecessor SAT query, but we first remove large literal
// blocks instead of spending one query per literal.
// Sampling on large SEC regressions showed clause generalization itself
// dominating runtime: many blocked cubes are not "huge", but they are already
// large enough that each extra predecessor SAT check costs far more than the
// slightly smaller learned clause saves later. Switch to the cheap-seed-only
// path earlier so medium ASIC cubes do not trigger a long literal-dropping
// search.
constexpr size_t kLargeBlockedCubeGeneralizationThreshold = 64;
// BlackParrot exact-PDR sampling showed a pathological loop where a 116-literal
// predecessor cube was repeatedly reduced to different 32-literal cheap seeds,
// each cheaply UNSAT at F[0] but too narrow to cover neighboring predecessors.
// Start with a smaller validated seed so those exact UNSAT probes learn broader
// frame clauses before PDR falls back to more expensive literal dropping.
constexpr size_t kLargeBlockedCubeSeedSize = 8;
constexpr size_t kMaxSmallBlockedCubeGeneralizationChecks = 8;
constexpr size_t kMaxLargeBlockedCubeGeneralizationChecks = 16;
// If a blocked cube's transition cone has only a tiny current-state/input
// surface, a few extra literal-dropping checks can pay for themselves. Keep the
// cap modest anyway: local BlackParrot samples showed this "cheap" path
// becoming the dominant runtime once the larger predecessor-core explosion was
// fixed.
constexpr size_t kCheapBlockedCubeTransitionSupportLimit = 8;
constexpr size_t kMaxCheapBlockedCubeGeneralizationChecks = 32;
constexpr size_t kMaxGeneralizedBlockedCubeTransitionSupport = 32;
// Clause generalization is optional. A sampled BlackParrot SEC/PDR run showed
// the final exact stage repeatedly trying to shrink already-blocked 116-literal
// cubes with broad transition support; almost every predecessor core collapsed
// to a tiny cube that still had a predecessor, so the engine spent its runtime
// rebuilding SAT queries without learning a useful stronger clause. For very
// large broad-support cubes, learn the proven cube verbatim and let later frame
// propagation decide whether more precision is actually needed.
constexpr size_t kVeryLargeBlockedCubeGeneralizationBypassThreshold = 96;
// Predecessor-core extraction is optional clause strengthening. Samples show
// it pays near the reset/init frontier, where a small core blocks many nearby
// abstract predecessors. Deeper frames already carry many learned clauses; the
// same core oracle can dominate runtime while trying to shrink an already-safe
// blocked cube, so learn the proven cube verbatim there.
constexpr size_t kMaxPredecessorCoreGeneralizationLevel = 2;
constexpr long long kPredecessorCoreConflictLimit = 10000;
// The solver's final conflict can be too coarse to use directly as a target-cube
// core in the PDR predecessor oracle. When that happens, stay inside the same
// already-built target-context solver and shrink the full target assumption set
// by deletion. These checks reuse the solver; unlike ordinary cube
// generalization they do not rebuild transition/frame CNF per trial.
constexpr size_t kMaxPredecessorCoreContextMinimizationChecks = 32;
// Broad dual-rail transition cones can make predecessor-core extraction too
// expensive, but BlackParrot shows a smaller shape where the cube support is
// only local (dozens of symbols) and skipping the core makes PDR enumerate
// sibling blockers. Try the core oracle for those local cones only.
constexpr size_t kMaxLocalDualRailPredecessorCoreSupport = 128;
constexpr size_t kMinLocalDualRailPredecessorCoreTargetSize = 4;
// BlackParrot sampling later found the same predecessor-core need below the
// "large cube" threshold: level-zero blockers around 37-49 literals with
// thousands of transition-support symbols were learned verbatim and then
// rediscovered one valuation at a time.  Try the core oracle for medium cubes
// only when their transition surface is already too broad for bounded
// literal-dropping to be worthwhile.
// AES sampling found the same broad-support blocker pattern at 12 literals:
// PDR repeatedly proved 12-literal, 113-support level-zero predecessor cubes
// UNSAT and learned them verbatim. Let the predecessor-core oracle cover that
// medium shape before the engine starts enumerating neighboring blockers.
constexpr size_t kMinMediumCubePredecessorCoreTargetSize = 8;
// Projected predecessor queries are allowed to ignore some learned frame
// clauses: that only weakens the SAT query, which can create extra obligations
// but cannot justify an unsound blocked cube. Large ASIC SEC runs can learn
// thousands of local frame clauses, and materializing all of them per query
// turns each predecessor check back into a near-global proof.
// Later steady-state samples on BlackParrot showed projected predecessor
// queries spending a large fraction of time just re-materializing learned
// frame clauses.  Projected PDR is allowed to under-approximate those clauses:
// skipping some only weakens the query and can at worst create extra
// obligations. Keep the per-query learned-frame surface small enough that the
// predecessor SAT work dominates again instead of clause streaming.
// BlackParrot measurements showed that a 128-clause cap was too aggressive:
// the query became cheaper to encode, but PDR then spent minutes solving
// tens of thousands of predecessors already blocked by omitted frame clauses.
// Keep projection bounded, but let a local ASIC cone see enough of its learned
// frame that the CEGAR refinement loop remains the exception rather than the
// steady state.
constexpr size_t kDefaultMaxProjectedFrameClausesPerQuery = 1024;
constexpr size_t kDefaultMaxProjectedFrameLiteralsPerQuery = 8192;
// If a projected-frame bad query keeps rediscovering the exact same bad cube,
// the learned blocker is outside the projected clause view.  Treat that as a
// local proof budget miss so the SEC strategy can split or skip the hard slice.
constexpr size_t kDefaultMaxRepeatedProjectedBadCubeHits = 64;
// Projected-frame CEGAR is useful for a few missing learned clauses, but
// BlackParrot sampling showed it can otherwise spend thousands of SAT queries
// adding local blockers for the same obligation before falling back to exact
// frames anyway. Cap the local repair loop and retry that obligation with the
// complete learned frame once projection is clearly too weak.
constexpr size_t kDefaultMaxProjectedFrameRefinementsBeforeExactRetry = 16;
// F[0] reset-frontier refinement is different from ordinary predecessor
// generalization: every dropped literal is guarded by an exact reset-image SAT
// query, and weak F[0] clauses can otherwise make PDR enumerate thousands of
// abstract reset states one cube at a time. Keep the pass bounded, but allow
// enough drops to minimize the small projected cubes PDR normally learns at
// level zero.
// Reset-frontier literal dropping is exact, but each trial can require a
// multi-frame reset-image SAT query.  BlackParrot sampling showed this pass
// dominating runtime and memory once reset bootstrap was correctly enabled, so
// keep only a small amount of safe weakening and let normal PDR blocking handle
// the rest.
constexpr size_t kMaxResetFrontierGeneralizationAttempts = 2;
// When an exact reset-frontier check proves cube U unreachable at concrete
// step N, the next PDR query often asks whether a neighboring cube C is
// reachable at N+1.  Before rebuilding the whole reset prefix, prove locally
// whether C's one-step predecessors imply U.  The proof is exact when it
// returns UNSAT, but it is deliberately capped because it is only a shortcut.
constexpr size_t kMaxPreviousResetCoreImplicationCoreLiterals = 8;
constexpr size_t kMaxPreviousResetCoreImplicationSupport = 1024;
constexpr size_t kMaxPreviousResetCoreImplicationChecks = 8;
constexpr size_t kMaxPriorResetCoreSpecializedProbes = 32;
constexpr size_t kMaxTransitionImpossibleResetCoreLiterals = 4;
constexpr size_t kMaxTransitionImpossibleResetCoreSupport = 1024;
constexpr size_t kMaxPdrResetUnreachableCoresPerStep = 4096;
constexpr size_t kMaxExactResetPredecessorCoreDeletionChecks = 8;
constexpr size_t kMaxExactResetPredecessorBadCubeLimit = 6;
constexpr size_t kMaxExactResetPredecessorSiblingCoreChecks = 32;
constexpr unsigned kPreviousResetCoreImplicationConflictLimit = 20000;
constexpr unsigned kTransitionImpossibleResetCoreConflictLimit = 20000;
// A projected predecessor path can reach Init even when the original bad cube
// is not reachable in the concrete bounded transition system.  When that
// happens, spend a small exact-SAT budget generalizing the unreachable root
// cube before learning the refinement; this blocks whole neighborhoods of
// spurious roots instead of rediscovering them one valuation at a time.
// The exact post-reset predecessor precheck is valuable when one concrete
// reset-image query can replace many abstract F[0] predecessor/refinement
// loops. The original Glucose-backed assumption flow needed a tight cap, but
// CaDiCaL can reuse the cached reset-frontier assumption solver cheaply enough
// for the wider BlackParrot cones that otherwise enumerate thousands of
// abstract predecessors.
constexpr size_t kMaxGlucoseExactResetPrecheckTransitionSupport = 256;
// sky130hd_riscv32i reset-frontier roots measure at 4128 transition-support
// symbols.  Let CaDiCaL's reusable assumption solver handle that still-local
// cone instead of falling back to thousands of sibling projected PDR cubes.
constexpr size_t kMaxCadicalExactResetPrecheckTransitionSupport = 8192;
constexpr size_t kDefaultPdrStatsInterval = 1000;
constexpr size_t kInitialPdrStatsQueries = 20;
// Query-result caching is an accelerator only.  Keep it bounded so a long SEC
// run cannot trade the predecessor-encoding wall for unbounded retained cubes.
constexpr size_t kMaxPredecessorQueryResultCacheEntries = 64 * 1024;
constexpr size_t kMaxPredecessorUnsatCoresPerContext = 4096;
constexpr size_t kMaxPredecessorClosedSymbolCacheEntries = 4096;
constexpr size_t kMaxPredecessorTargetSurfaceCacheEntries = 4096;
constexpr size_t kMaxProcessResetUnreachableCoreCacheEntries = 4;
// FrameFormulaEncoder already makes a small generic Tseitin reservation, but
// sampled dual-rail PDR leaves still spent most time growing CaDiCaL variable
// vectors while streaming known-large transition cones. Reserve a larger,
// bounded chunk from PDR when we have the transition DAG estimate.
constexpr size_t kMinPdrTransitionSolverReserveNodes = 64 * 1024;
constexpr size_t kMaxPdrTransitionSolverReserveHint = 512 * 1024;
// PDR can use inferred state correspondences as an ordinary frame invariant,
// but ASIC retiming/optimization can make a few inferred pairs non-inductive
// while many others are still valid and very useful.  Mine a validated subset
// once per PDR run instead of forcing the blocking loop to rediscover thousands
// LCOV_EXCL_START
// of those equality clauses one cube at a time.
constexpr size_t kMaxStateEqualitySubsetPairs = 2048;
constexpr size_t kMaxStateEqualitySubsetIterations = 256;
// LCOV_EXCL_STOP

bool isLocalDualRailPredecessorCoreSurface(size_t level,
                                           size_t cubeSize,
                                           size_t transitionSupportSize) {
  return level <= 1 &&
         cubeSize >= kMinLocalDualRailPredecessorCoreTargetSize &&
         transitionSupportSize <= kMaxLocalDualRailPredecessorCoreSupport;
}

// Cubes represent a concrete bad/predecessor state, while clauses are the
// blocked generalization of such a state stored in a PDR frame.
struct CubeLiteral {  // LCOV_EXCL_LINE
  size_t symbol = 0;  // LCOV_EXCL_LINE
  bool value = false;  // LCOV_EXCL_LINE

  bool operator==(const CubeLiteral& other) const {
    return symbol == other.symbol && value == other.value;
  }
};

struct CubeLiteralHash {
  size_t operator()(const CubeLiteral& literal) const {
    return std::hash<size_t>()(
        (literal.symbol << 1) ^ (literal.value ? 1ULL : 0ULL));
  }
};

struct ClauseLiteral {
  size_t symbol = 0;
  bool positive = false;

  bool operator==(const ClauseLiteral& other) const {
    return symbol == other.symbol && positive == other.positive;
  }
};

using StateCube = std::vector<CubeLiteral>;
using StateClause = std::vector<ClauseLiteral>;

void mixHashValue(size_t& seed, size_t value) {
  seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
}

struct StateCubeHash {
  size_t operator()(const StateCube& cube) const {
    size_t seed = 0x9e3779b97f4a7c15ULL;
    for (const auto& literal : cube) {
      mixHashValue(seed, CubeLiteralHash{}(literal));
    }
    return seed;
  }
};

struct StateClauseHash {
  size_t operator()(const StateClause& clause) const {
    size_t seed = 0x517cc1b727220a95ULL;
    for (const auto& literal : clause) {
      mixHashValue(seed, std::hash<size_t>()(literal.symbol));
      mixHashValue(seed, std::hash<bool>()(literal.positive));
    }
    return seed;
  }
// LCOV_EXCL_START
};

bool cubeLiteralLess(const CubeLiteral& lhs, const CubeLiteral& rhs) {
  return detail::pdrCubeLiteralOrderLess(
      lhs.symbol, lhs.value, rhs.symbol, rhs.value);
}

bool clauseLiteralLess(const ClauseLiteral& lhs, const ClauseLiteral& rhs) {
  if (lhs.symbol != rhs.symbol) {
    return lhs.symbol < rhs.symbol;
  }
  return lhs.positive < rhs.positive;
}

bool stateCubeLess(const StateCube& lhs, const StateCube& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), cubeLiteralLess);
}

bool stateClauseLess(const StateClause& lhs, const StateClause& rhs) {
  if (lhs.size() != rhs.size()) {
    return lhs.size() < rhs.size();
  }
  return std::lexicographical_compare(
      lhs.begin(), lhs.end(), rhs.begin(), rhs.end(), clauseLiteralLess);
}

void sortStateCubesDeterministically(std::vector<StateCube>& cubes) {
  std::sort(cubes.begin(), cubes.end(), stateCubeLess);
}

void sortStateClausesDeterministically(std::vector<StateClause>& clauses) {
  std::sort(clauses.begin(), clauses.end(), stateClauseLess);
}

struct StateClauseSetKey {  // LCOV_EXCL_LINE
// LCOV_EXCL_STOP
  size_t targetFrame = 0;
  std::vector<StateClause> clauses;

  bool operator==(const StateClauseSetKey& other) const {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return targetFrame == other.targetFrame &&  // LCOV_EXCL_LINE
           clauses == other.clauses;  // LCOV_EXCL_LINE
  }
};
// LCOV_EXCL_STOP

// LCOV_EXCL_START
struct StateClauseSetKeyHash {
// LCOV_EXCL_STOP
  size_t operator()(const StateClauseSetKey& key) const {  // LCOV_EXCL_LINE
    size_t seed = std::hash<size_t>()(key.targetFrame);  // LCOV_EXCL_LINE
    for (const auto& clause : key.clauses) {  // LCOV_EXCL_LINE
      mixHashValue(seed, StateClauseHash{}(clause));  // LCOV_EXCL_LINE
    }
    return seed;  // LCOV_EXCL_LINE
  }
};

struct ResetFrontierCubeKey {  // LCOV_EXCL_LINE
  size_t postBootstrapSteps = 0;
  StateCube cube;

  bool operator==(const ResetFrontierCubeKey& other) const {
    return postBootstrapSteps == other.postBootstrapSteps &&
           cube == other.cube;
  }
};

struct ResetFrontierCubeKeyHash {
  size_t operator()(const ResetFrontierCubeKey& key) const {
    size_t seed = std::hash<size_t>()(key.postBootstrapSteps);
    mixHashValue(seed, StateCubeHash{}(key.cube));
    return seed;
  }
};

struct ResetExpressionConflictKey {
  ResetFrontierCubeKey frontier;
  const BoolExpr* frameInvariant = nullptr;

  bool operator==(const ResetExpressionConflictKey& other) const {
    return frontier == other.frontier &&
           frameInvariant == other.frameInvariant;
  }
};

struct ResetExpressionConflictKeyHash {
  size_t operator()(const ResetExpressionConflictKey& key) const {
    size_t seed = ResetFrontierCubeKeyHash{}(key.frontier);
    mixHashValue(seed, std::hash<const void*>()(key.frameInvariant));
    return seed;
  }
};

struct ObservedOutputBadClauseGroup {
  size_t outputIndex = 0;
  BoolExpr* outputBad = nullptr;
  std::vector<StateClause> clauses;
};

struct FrameClauses {
  // F[i] stores clauses known to hold for all states reachable within i steps.
  std::vector<StateClause> clauses;
  // Cached SAT queries can keep old, subsumed clauses soundly; they only need
  // to see every newly learned clause.  Keep an append-only log so they can
  // synchronize by delta instead of rescanning ASIC-size frames after each
  // local refinement.
  std::vector<StateClause> addedClauseLog;
  // Lazily maps a state symbol to the learned clauses mentioning it. PDR asks
  // many local SAT queries against the same frame, so this cache lets each
  // query pull only the clauses touching its cone instead of rescanning the
  // entire learned frame history.
  mutable bool clauseIndexDirty = true;
  mutable std::unordered_map<size_t, std::vector<size_t>> clauseIndicesBySymbol;
  // Scratch epoch marks used while emitting relevant clauses into one SAT
  // query.  This avoids materializing and sorting a giant candidate-index list
  // when many query symbols touch overlapping learned clauses.
  mutable uint64_t clauseEmitEpoch = 1;
  mutable std::vector<uint64_t> clauseEmitEpochByIndex;
};

size_t frameClausesFingerprint(const std::vector<FrameClauses>& frames,
                               size_t level) {
  if (level >= frames.size()) {
    return 0; // LCOV_EXCL_LINE
  }
  size_t seed = std::hash<size_t>()(level);
  const auto& frame = frames[level];
  mixHashValue(seed, std::hash<size_t>()(frame.clauses.size()));
  for (const auto& clause : frame.clauses) {
    mixHashValue(seed, StateClauseHash{}(clause));
  }
  return seed;
}

size_t extraFrameClausesFingerprint(
    const std::vector<StateClause>* extraFrameClauses) {
  if (extraFrameClauses == nullptr) {
    return 0;
  }
  // Projected retry clauses are local to one predecessor obligation.  Include
  // their ordered content in the result-cache key so repeated retries can hit
  // the cache without sharing answers with the base frame query.
  return detail::pdrOrderedClauseFingerprint(*extraFrameClauses); // LCOV_EXCL_LINE
}

uint64_t nextClauseEmitEpoch(const FrameClauses& frameClauses);

struct ComplementPartnerIndex {
  std::unordered_map<size_t, std::vector<size_t>> partnersBySymbol;

  explicit ComplementPartnerIndex(const KInductionProblem& problem) {
    partnersBySymbol.reserve(
        2 * (problem.complementedStatePairs0.size() +
             problem.complementedStatePairs1.size()));
    addPairs(problem.complementedStatePairs0);
    addPairs(problem.complementedStatePairs1);
  }

 private:
  void addPairs(const std::vector<std::pair<size_t, size_t>>& pairs) {
    for (const auto& [primarySymbol, complementedSymbol] : pairs) {
      partnersBySymbol[primarySymbol].push_back(complementedSymbol);
      partnersBySymbol[complementedSymbol].push_back(primarySymbol);
    }
  }
};

struct ProofObligation {
  // "cube is bad at level" requests either a predecessor or a blocking clause.
  StateCube cube;
  size_t level = 0;
  size_t badFrame = 0;
  // The original frontier cube this obligation is trying to block.  Projected
  // predecessor cubes are useful for fast blocking, but if such a projection
  // reaches Init we validate the root cube against the concrete bounded
  // transition prefix before reporting a counterexample.
  StateCube rootCube;
};

struct ProofObligationKey {
  size_t level = 0;
  size_t badFrame = 0;
  StateCube cube;
  StateCube rootCube;

  bool operator==(const ProofObligationKey& other) const {
    return level == other.level &&
           badFrame == other.badFrame &&
           cube == other.cube &&
           rootCube == other.rootCube;
  }
};

struct ProofObligationKeyHash {
  size_t operator()(const ProofObligationKey& key) const {
    size_t seed = std::hash<size_t>()(key.level);
    mixHashValue(seed, std::hash<size_t>()(key.badFrame));
    mixHashValue(seed, StateCubeHash{}(key.cube));
    mixHashValue(seed, StateCubeHash{}(key.rootCube));
    return seed;
  }
};

struct JustificationBudget {
  size_t remainingVisits = 0;
  size_t maxAssignments = 0;
  bool exhausted = false;
};

struct SymbolPair {
  size_t first = 0;
  size_t second = 0;

  bool operator==(const SymbolPair& other) const {
    return first == other.first && second == other.second;
  }
};

struct SymbolPairHash {
  size_t operator()(const SymbolPair& pair) const {
    // Splitmix-style mixing keeps pair lookup cheap and avoids repeatedly
    // scanning thousands of extracted startup equalities during PDR seeding.
    size_t seed = pair.first + 0x9e3779b97f4a7c15ULL;
    seed ^= pair.second + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
    return seed;
  }
};

class InitParityRelations {
 public:
  void ensureSymbol(size_t symbol) {
    if (parent_.find(symbol) == parent_.end()) {
      parent_.emplace(symbol, symbol);
      parityToParent_.emplace(symbol, false);
    }
  }

  void addEquality(size_t lhs, size_t rhs) { unite(lhs, rhs, false); }

  void addComplement(size_t lhs, size_t rhs) { unite(lhs, rhs, true); }

  std::optional<std::pair<size_t, bool>> findWithParity(size_t symbol) const {
    const auto parentIt = parent_.find(symbol);
    if (parentIt == parent_.end()) {
      return std::nullopt;
    }
    const size_t parent = parentIt->second;
    // LCOV_EXCL_START
    const bool parity = parityToParent_.at(symbol);
    // LCOV_EXCL_STOP
    if (parent == symbol) {
      return std::pair{symbol, false};
    }
    const auto parentRoot = findWithParity(parent);
    if (!parentRoot.has_value()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    return std::pair{parentRoot->first, parity ^ parentRoot->second};
  }

 private:
  std::pair<size_t, bool> mutableFind(size_t symbol) {
    // LCOV_EXCL_START
    ensureSymbol(symbol);
    const size_t parent = parent_[symbol];
    const bool parity = parityToParent_[symbol];
    if (parent == symbol) {
    // LCOV_EXCL_STOP
      return {symbol, false};
    }
    const auto root = mutableFind(parent);  // LCOV_EXCL_LINE
    parent_[symbol] = root.first;  // LCOV_EXCL_LINE
    parityToParent_[symbol] = parity ^ root.second;  // LCOV_EXCL_LINE
    return {parent_[symbol], parityToParent_[symbol]};  // LCOV_EXCL_LINE
  }

  void unite(size_t lhs, size_t rhs, bool inverted) {
    const auto lhsRoot = mutableFind(lhs);
    const auto rhsRoot = mutableFind(rhs);
    if (lhsRoot.first == rhsRoot.first) {
      return; // LCOV_EXCL_LINE
    }
    parent_[lhsRoot.first] = rhsRoot.first;
    // value(lhs) xor value(rhs) must equal `inverted`.
    parityToParent_[lhsRoot.first] =
        lhsRoot.second ^ rhsRoot.second ^ inverted;
  }

  std::unordered_map<size_t, size_t> parent_;
  std::unordered_map<size_t, bool> parityToParent_;
};

struct ExprPair {
  BoolExpr* first = nullptr;
  BoolExpr* second = nullptr;

  bool operator==(const ExprPair& other) const {
    return first == other.first && second == other.second;
  }
};

struct ExprPairHash {
  size_t operator()(const ExprPair& pair) const {
    size_t seed =
        reinterpret_cast<size_t>(pair.first) + 0x9e3779b97f4a7c15ULL;
    seed ^= reinterpret_cast<size_t>(pair.second) +
            0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
    return seed;
  }
};

struct InitFactIndex {
  std::unordered_map<size_t, bool> assignments;
  std::unordered_map<size_t, bool> rootAssignments;
  std::unordered_set<SymbolPair, SymbolPairHash> equalities;
  std::unordered_set<SymbolPair, SymbolPairHash> complements;
  InitParityRelations relations;
};

struct ResetExpressionConflictMemoEntry {
  bool hasConflict = false;
  StateCube conflict;
};

struct TransitionAssumptionKey {
  size_t transitionSymbol = 0;
  bool desiredValue = false;

  bool operator==(const TransitionAssumptionKey& other) const {
    return transitionSymbol == other.transitionSymbol &&
           desiredValue == other.desiredValue;
  }
};

struct TransitionAssumptionKeyHash {
  size_t operator()(const TransitionAssumptionKey& key) const {
    size_t seed = std::hash<size_t>()(key.transitionSymbol);
    mixHashValue(seed, std::hash<bool>()(key.desiredValue));
    return seed;
  }
};

struct PredecessorQueryResultKey { // LCOV_EXCL_LINE
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  size_t extraFrameFingerprint = 0;
  bool exactFrameClauses = false;
  bool excludeTargetOnCurrentFrame = false;
  size_t predecessorProjectionLimit = 0;
  StateCube targetCube;

  bool operator==(const PredecessorQueryResultKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
           extraFrameFingerprint == other.extraFrameFingerprint &&
           exactFrameClauses == other.exactFrameClauses &&
           excludeTargetOnCurrentFrame == other.excludeTargetOnCurrentFrame &&
           predecessorProjectionLimit == other.predecessorProjectionLimit &&
           targetCube == other.targetCube;
  }
};

struct PredecessorQueryResultKeyHash {
  size_t operator()(const PredecessorQueryResultKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, std::hash<const void*>()(key.initFormula));
    mixHashValue(seed, std::hash<const void*>()(key.frameInvariant));
    mixHashValue(seed, std::hash<size_t>()(key.level));
    mixHashValue(seed, std::hash<size_t>()(key.frameFingerprint));
    mixHashValue(seed, std::hash<size_t>()(key.extraFrameFingerprint));
    mixHashValue(seed, std::hash<bool>()(key.exactFrameClauses));
    mixHashValue(seed, std::hash<bool>()(key.excludeTargetOnCurrentFrame));
    mixHashValue(seed, std::hash<size_t>()(key.predecessorProjectionLimit));
    mixHashValue(seed, StateCubeHash{}(key.targetCube));
    return seed;
  }
};

struct PredecessorQueryResultEntry {
  bool hasPredecessor = false;
  StateCube predecessor;
  bool hasUnsatCore = false;
  StateCube unsatCore;
};

struct PredecessorUnsatCoreCacheKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t extraFrameFingerprint = 0;
  bool exactFrameClauses = false;
  bool excludeTargetOnCurrentFrame = false;
  size_t predecessorProjectionLimit = 0;

  bool operator==(const PredecessorUnsatCoreCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           extraFrameFingerprint == other.extraFrameFingerprint &&
           exactFrameClauses == other.exactFrameClauses &&
           excludeTargetOnCurrentFrame == other.excludeTargetOnCurrentFrame &&
           predecessorProjectionLimit == other.predecessorProjectionLimit;
  }
};

struct PredecessorUnsatCoreCacheKeyHash {
  size_t operator()(const PredecessorUnsatCoreCacheKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, std::hash<const void*>()(key.initFormula));
    mixHashValue(seed, std::hash<const void*>()(key.frameInvariant));
    mixHashValue(seed, std::hash<size_t>()(key.level));
    mixHashValue(seed, std::hash<size_t>()(key.extraFrameFingerprint));
    mixHashValue(seed, std::hash<bool>()(key.exactFrameClauses));
    mixHashValue(seed, std::hash<bool>()(key.excludeTargetOnCurrentFrame));
    mixHashValue(seed, std::hash<size_t>()(key.predecessorProjectionLimit));
    return seed;
  }
};

class PdrFormulaSupportCache;

struct PredecessorFrameSymbolSurfaceKey {
  const KInductionProblem* problem = nullptr;
  BoolExpr* initFormula = nullptr;
  BoolExpr* frameInvariant = nullptr;
  const ComplementPartnerIndex* complementPartners = nullptr;
  const PdrFormulaSupportCache* supportCache = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  bool exactFrameClauses = false;

  bool operator==(const PredecessorFrameSymbolSurfaceKey& other) const { // LCOV_EXCL_LINE
    return problem == other.problem && // LCOV_EXCL_LINE
           initFormula == other.initFormula && // LCOV_EXCL_LINE
           frameInvariant == other.frameInvariant && // LCOV_EXCL_LINE
           complementPartners == other.complementPartners && // LCOV_EXCL_LINE
           supportCache == other.supportCache && // LCOV_EXCL_LINE
           level == other.level && // LCOV_EXCL_LINE
           frameFingerprint == other.frameFingerprint && // LCOV_EXCL_LINE
           exactFrameClauses == other.exactFrameClauses; // LCOV_EXCL_LINE
  }
};

struct PredecessorFrameSymbolSurface {
  bool valid = false;
  PredecessorFrameSymbolSurfaceKey key;
  std::vector<size_t> symbols;
};

struct SymbolVectorHash {
  size_t operator()(const std::vector<size_t>& symbols) const {
    size_t seed = std::hash<size_t>()(symbols.size());
    for (const auto symbol : symbols) {
      mixHashValue(seed, std::hash<size_t>()(symbol));
    }
    return seed;
  }
};

struct PredecessorTargetSurfaceKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  StateCube targetCube;

  bool operator==(const PredecessorTargetSurfaceKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           targetCube == other.targetCube;
  }
};

struct PredecessorTargetSurfaceKeyHash {
  size_t operator()(const PredecessorTargetSurfaceKey& key) const {
    size_t seed = std::hash<const void*>()(key.problem);
    mixHashValue(seed, std::hash<const void*>()(key.transitionByState));
    mixHashValue(seed, StateCubeHash{}(key.targetCube));
    return seed;
  }
};

struct PredecessorTargetSurface { // LCOV_EXCL_LINE
  std::vector<size_t> targetSymbols;
  std::vector<size_t> encodedTargets;
  std::vector<size_t> transitionSupportSymbols;
  size_t transitionEncodingNodes = 0;
};

struct PredecessorAssumptionCacheKey {
  const KInductionProblem* problem = nullptr;
  const TransitionExprResolver* transitionByState = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  size_t frameFingerprint = 0;
  bool exactFrameClauses = false;
  std::vector<size_t> solverSymbols;

  bool operator==(const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           frameFingerprint == other.frameFingerprint &&
           exactFrameClauses == other.exactFrameClauses &&
           solverSymbols == other.solverSymbols;
  }

  bool hasSameReusableContext(
      const PredecessorAssumptionCacheKey& other) const {
    return problem == other.problem &&
           transitionByState == other.transitionByState &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           exactFrameClauses == other.exactFrameClauses &&
           solverSymbols == other.solverSymbols;
  }
};

struct PredecessorAssumptionSolver {
  PredecessorAssumptionCacheKey key;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
  // The cached SAT model is useful only if predecessor extraction can read the
  // transition-expression leaves that were encoded under assumptions.
  std::unordered_map<size_t, int> transitionLeafLits;
  std::unordered_map<TransitionAssumptionKey, int, TransitionAssumptionKeyHash>
      assumptionByTransitionLiteral;
  // Reuse the transition-DAG encoder together with the cached predecessor
  // solver. Neighboring dual-rail PDR targets often share most of the same
  // transition cone; keeping the encoder node cache avoids re-emitting that
  // Tseitin structure for every target literal.
  std::unordered_map<const std::unordered_map<size_t, size_t>*,
                     std::unique_ptr<FrameFormulaEncoder>>
      transitionEncoderBySymbolMap;
  std::unordered_set<size_t> querySymbolSet;
  std::unordered_set<StateClause, StateClauseHash> emittedFrameClauses;
  // Some predecessor checks also need "current state is not the target cube".
  // Keep those target-specific clauses behind selectors so the base solver can
  // be reused for neighboring queries without permanently excluding a cube.
  std::unordered_map<StateClause, int, StateClauseHash>
      exclusionAssumptionByClause;
  // Projected-frame retries add a few missing blockers around one obligation.
  // Selector assumptions let those local refinements reuse the same cached
  // predecessor solver instead of rebuilding a fresh exact SAT instance.
  std::unordered_map<StateClause, int, StateClauseHash>
      extraFrameAssumptionByClause;
};

struct PredecessorAssumptionCache {
  // PDR level-local predecessor queries share the same frame/bootstrap context
  // and differ mostly by target cube. Keep this separate from reset-frontier
  // caches so ordinary level-1 propagation/blocking queries can use it too.
  std::unique_ptr<PredecessorAssumptionSolver> solver;
  // Full predecessor-query result cache. SAT entries are keyed by the exact
  // frame fingerprint; UNSAT entries also get a fingerprint-free key because
  // PDR frames only strengthen over time, so a proven-empty predecessor set
  // remains empty after more clauses are learned.
  std::unordered_map<PredecessorQueryResultKey,
                     PredecessorQueryResultEntry,
                     PredecessorQueryResultKeyHash>
      queryResults;
  std::unordered_set<PredecessorQueryResultKey,
                     PredecessorQueryResultKeyHash>
      unsatQueries;
  // A predecessor UNSAT core for cube U also proves UNSAT for every later
  // target cube that contains U under the same PDR context. Keep those cores
  // separately from exact target results so neighboring dual-rail cubes can
  // reuse the proof without re-solving a wider assumption set.
  std::unordered_map<PredecessorUnsatCoreCacheKey,
                     std::vector<StateCube>,
                     PredecessorUnsatCoreCacheKeyHash>
      unsatCoresByContext;
  const TransitionExprResolver* widenedPredecessorCacheResolver = nullptr;
  // Local dual-rail leaves repeatedly ask nearly identical predecessor
  // questions.  Keep a monotonically widened cached-solver surface so a few
  // target-specific local support symbols do not force solver rebuilds.
  std::vector<size_t> widenedPredecessorCacheSymbols;
  PredecessorFrameSymbolSurface currentFrameSymbols;
  std::unordered_map<std::vector<size_t>,
                     std::vector<size_t>,
                     SymbolVectorHash>
      closedCurrentFrameSymbols;
  std::unordered_map<PredecessorTargetSurfaceKey,
                     PredecessorTargetSurface,
                     PredecessorTargetSurfaceKeyHash>
      targetSurfaces;
};

struct BadCubeAssumptionCacheKey {
  const KInductionProblem* problem = nullptr;
  const BoolExpr* initFormula = nullptr;
  const BoolExpr* frameInvariant = nullptr;
  size_t level = 0;
  bool exactFrameClauses = false;
  std::vector<size_t> solverSymbols;

  bool operator==(const BadCubeAssumptionCacheKey& other) const {
    return problem == other.problem &&
           initFormula == other.initFormula &&
           frameInvariant == other.frameInvariant &&
           level == other.level &&
           exactFrameClauses == other.exactFrameClauses &&
           solverSymbols == other.solverSymbols;
  }
};

struct BadCubeAssumptionSolver {
  BadCubeAssumptionCacheKey key;
  std::unique_ptr<SATSolverWrapper> solver;
  std::unique_ptr<FrameVariableStore> variables;
  std::unique_ptr<FrameFormulaEncoder> encoder;
  std::unordered_map<BoolExpr*, int> encodedBadRoots;
  std::unordered_set<size_t> querySymbolSet;
  std::unordered_set<StateClause, StateClauseHash> emittedFrameClauses;
  size_t emittedFrameFingerprint = 0;
  size_t emittedFrameLogOffset = 0;
};

struct BadCubeAssumptionCache {
  // Bad-cube searches repeatedly ask the same frame context with different
  // output-bad roots. Keep frame facts permanent and vary only the root
  // literal as a solver assumption.
  std::unique_ptr<BadCubeAssumptionSolver> solver;
};

class ResetSymbolicEvaluator;
class ResetExpressionCanonicalizer;
struct ResetBootstrapExpressionRelations;

struct ResetFrontierCache {
  // PDR can revisit the same abstract F[0] cube through multiple bad
  // obligations. Cache the exact reset-image answer so we do not rebuild the
  // same reset-prefix SAT query more than once per engine run.
  std::unordered_map<ResetFrontierCubeKey, bool, ResetFrontierCubeKeyHash>
      outsideByCubeKey;
  // The exact reset-frontier query also needs immutable per-problem indexes
  // for equality aliases and complemented-state lookup. Build them once per
  // blocking wave instead of rescanning ASIC-size equality tables per cube.
  std::shared_ptr<ResetFrontierReachabilityContext> reachabilityContext;
  BoolExpr* reachabilityFrameInvariant = nullptr;
  // The reset-specialized SAT shortcut substitutes post-reset state bits back
  // to frame-0 expressions. ASIC samples showed neighboring root cubes asking
  // for the same substituted expressions again and again, so keep this memoized
  // evaluator with the reset-frontier cache instead of rebuilding it per cube.
  std::shared_ptr<ResetSymbolicEvaluator> resetExpressionEvaluator;
  const KInductionProblem* resetExpressionProblem = nullptr;
  const TransitionExprResolver* resetExpressionTransitions = nullptr;
  // Canonicalizes substituted reset expressions under frame-0 SEC equalities.
  // This catches common ASIC reset-frontier contradictions before the
  // reset-specialized SAT query, avoiding repeated per-cube solver setup.
  std::shared_ptr<ResetExpressionCanonicalizer> resetExpressionCanonicalizer;
  const KInductionProblem* resetExpressionCanonicalizerProblem = nullptr;
  // Bootstrap equality expressions are independent of the queried cube. PDR's
  // validated bad-formula repair asks hundreds of neighboring reset cubes, so
  // cache the fixed-point expression rewriter instead of rebuilding it per cube.
  std::shared_ptr<ResetBootstrapExpressionRelations>
      resetBootstrapExpressionRelations;
  const KInductionProblem* resetBootstrapExpressionProblem = nullptr;
  const TransitionExprResolver* resetBootstrapExpressionTransitions = nullptr;
  // Mirrors the reset-frontier solver's unreachable-core cache in PDR's cube
  // type.  This lets the blocking loop run cheap one-step implication checks
  // against prior reset-frontier blockers before falling back to a full
  // reset-prefix BMC query.
  std::unordered_map<size_t, std::vector<StateCube>>
      resetUnreachableCoresByPostBootstrapStep;
  // Some reset cores are stronger than a bounded reset-frontier fact: the
  // post-reset transition relation cannot produce them from any predecessor
  // state. Once proved, any later concrete-frame check containing such a core
  // can skip rebuilding the reset-prefix solver.
  std::unordered_map<StateCube, bool, StateCubeHash>
      transitionImpossibleResetCoreByKey;
  std::vector<StateCube> transitionImpossibleResetCores;
  // Reset-expression conflict proofs are local to a target post-reset step and
  // cube. Validated bad-formula repair asks many overlapping pair/triple/full
  // cube questions, so memoize both proved conflicts and misses.
  std::unordered_map<
      ResetExpressionConflictKey,
      ResetExpressionConflictMemoEntry,
      ResetExpressionConflictKeyHash>
      resetExpressionConflictByKey;
  // Once a deep reset-expression shortcut is rejected for budget/support, later
  // deeper frames should not rebuild the same huge optional reset cone.
  std::unordered_map<ResetFrontierCubeKey, size_t, ResetFrontierCubeKeyHash>
      resetExpressionBudgetSkipFromStep;
  // Deep single-output bad-formula validation is an exact proof, but it can be
  // expensive. If it fails to prove unreachable for a given local bad CNF, do
  // not retry the same proof every time PDR rediscovers a neighboring root.
  std::unordered_set<StateClauseSetKey, StateClauseSetKeyHash>
      wholeBadFormulaValidationMisses;
  // Validated bad-formula repair may revisit many projected root cubes for
  // the same PDR problem. The per-output bad predicates are immutable across
  // those attempts, so build their small CNFs once per engine run.
  bool observedOutputBadClauseCacheBuilt = false;
  std::vector<ObservedOutputBadClauseGroup> observedOutputBadClauseGroups;
  std::optional<std::vector<StateClause>> observedOutputBadClauses;
};

bool hasLargeDualRailResetFrontierSurface(const KInductionProblem& problem);

enum class ConcreteCubeReachabilityMode {
  CachedAssumptions,
  OneShotUnitClauses,
};

enum class PdrBudgetExhaustion {
  None,
  LocalQuery,
  ProjectedCounterexampleRefinement,
  RepeatedProjectedBadCube,
};

thread_local PdrBudgetExhaustion pdrBudgetExhaustion =
    PdrBudgetExhaustion::None;
thread_local size_t pdrPredecessorQueryLimit = 0;
thread_local size_t pdrProjectedCounterexampleRefinementLimit = 0;

bool pdrStatsEnabled();

void resetPdrBudgetExhaustion() {
  pdrBudgetExhaustion = PdrBudgetExhaustion::None;
}

void setPdrProjectedCounterexampleRefinementLimit(size_t limit) {
  pdrProjectedCounterexampleRefinementLimit = limit;
}

void setPdrPredecessorQueryLimit(size_t limit) {
  pdrPredecessorQueryLimit = limit;
}

void markPdrBudgetExhausted(PdrBudgetExhaustion reason) {
  if (pdrBudgetExhaustion == PdrBudgetExhaustion::None) {
    pdrBudgetExhaustion = reason;
    if (reason == PdrBudgetExhaustion::ProjectedCounterexampleRefinement &&
        pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: projected counterexample repair budget exhausted ",
          "refinement_limit=",
          pdrProjectedCounterexampleRefinementLimit);
    }
  }
}

bool hasPdrBudgetExhaustion() {
  return pdrBudgetExhaustion != PdrBudgetExhaustion::None;
}

bool consumePdrPredecessorQueryBudget(size_t* remainingQueries) {
  if (remainingQueries == nullptr) {
    return true;
  }
  if (*remainingQueries == 0) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor query-count budget exhausted limit=",
          pdrPredecessorQueryLimit);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  --(*remainingQueries);
  return true;
}

// LCOV_EXCL_START
void consumeProjectedCounterexampleRefinementBudget(
// LCOV_EXCL_STOP
    size_t* remainingRefinements) {
  if (remainingRefinements == nullptr) {
    return;
  }
  if (*remainingRefinements == 0) {
    markPdrBudgetExhausted( // LCOV_EXCL_LINE
        PdrBudgetExhaustion::ProjectedCounterexampleRefinement);  // LCOV_EXCL_LINE
    return;  // LCOV_EXCL_LINE
  }
  --(*remainingRefinements);
  if (*remainingRefinements == 0) {
    markPdrBudgetExhausted(
        PdrBudgetExhaustion::ProjectedCounterexampleRefinement);  // LCOV_EXCL_LINE
  }
}

bool pdrStatsEnabled() {
  return std::getenv("KEPLER_SEC_PDR_STATS") != nullptr;
}

size_t pdrDualRailStateSymbolCount(const KInductionProblem& problem) {
  return problem.dualRailStatePairs.size() * 2;
}

size_t pdrTransitionSourceCount(const KInductionProblem& problem) {
  size_t count = problem.transitions0.size() + problem.transitions1.size();
  if (problem.lazyTransitions != nullptr) {
    count += problem.lazyTransitions->sourceByStateSymbol.size();
  }
  return count;
}

size_t pdrOriginalObservedOutputCount(const KInductionProblem& problem) {
  return problem.originalObservedOutputCount == 0
             ? problem.observedOutputExprs0.size()
             : problem.originalObservedOutputCount;
}

bool hasBroadDualRailResidualOutputSurface(const KInductionProblem& problem) {
  return detail::isBroadDualRailResidualOutputSurface(
      problem.usesDualRailStateEncoding,
      problem.observedOutputExprs0.size(),
      pdrOriginalObservedOutputCount(problem),
      kMaxExactResetFrontierDualRailOriginalOutputs);
}

bool hasLocalDualRailFinalLeafRepairSurface(const KInductionProblem& problem) {
  return hasBroadDualRailResidualOutputSurface(problem) &&
         pdrDualRailStateSymbolCount(problem) <=
             kMaxLocalDualRailFinalLeafRepairStateSymbols;
}

bool canRepairLocalDualRailFinalLeafRoot(const KInductionProblem& problem,
                                         const StateCube& rootCube) {
  return hasLocalDualRailFinalLeafRepairSurface(problem) &&
         rootCube.size() <= kMaxLocalDualRailFinalLeafRepairRootLiterals;
}

bool usesLocalDualRailFinalLeafRepairBudgets(
    const KInductionProblem& problem,
    bool useExactFrameClauses,
    bool refineProjectedCounterexamples) {
  return hasLocalDualRailFinalLeafRepairSurface(problem) &&
         useExactFrameClauses &&
         refineProjectedCounterexamples;
}

bool canRetryDualRailPredecessorInCachedSolver(
    const KInductionProblem& problem) {
  return hasLocalDualRailFinalLeafRepairSurface(problem);
}

bool canUsePredecessorQueryResultCache(const KInductionProblem& problem) {
  if (!problem.usesDualRailStateEncoding) {
    return false;
  }
  const size_t observedOutputs = problem.observedOutputExprs0.size();
  const size_t originalOutputs = pdrOriginalObservedOutputCount(problem);
  // Medium residual slices, such as AES 129->1 output leaves, must stay on the
  // 376a017 path: cached assumptions may probe cheaply, but the predecessor
  // answer/core itself is recomputed by the ordinary exact query. Non-residual
  // unit fixtures and broad residual leaves keep the cache path.
  return !(originalOutputs > observedOutputs &&
           originalOutputs <= kMaxExactResetFrontierDualRailOriginalOutputs);
}

bool canUseResidualExactResetCubeBatch(const KInductionProblem& problem) { // LCOV_EXCL_LINE
  // The residual exact reset-cube batch is a memory/perf shortcut for leaves
  // split from broad output buses. AES also becomes a one-output leaf, but the
  // good 376a017 route uses partial reset-conflict refinement there; batching
  // the residual exact check changed the learned-frame shape and regressed AES.
  return hasBroadDualRailResidualOutputSurface(problem); // LCOV_EXCL_LINE
}

size_t effectiveLocalDualRailFinalLeafBudget(size_t configuredBudget,
                                             size_t localMinimum) {
  if (configuredBudget == 0) {
    return 0;
  }
  return std::max(configuredBudget, localMinimum); // LCOV_EXCL_LINE
}

size_t effectiveLocalDualRailFinalLeafProjectionLimit(size_t configuredLimit) {
  if (configuredLimit == 0) {
    return 0; // LCOV_EXCL_LINE
  }
  return std::max(configuredLimit,
                  kMinLocalDualRailFinalLeafPredecessorProjection);
}

size_t effectiveLocalDualRailFinalLeafEncodingSupportLimit(
    size_t configuredLimit) {
  if (configuredLimit == 0) {
    return 0; // LCOV_EXCL_LINE
  }
  return std::max(configuredLimit,
                  kMinLocalDualRailFinalLeafPredecessorSupport);
}

KEPLER_FORMAL::Config::SolverType localDualRailPredecessorSolverType(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType configuredSolverType) {
  if (hasLocalDualRailFinalLeafRepairSurface(problem) &&
      configuredSolverType == KEPLER_FORMAL::Config::SolverType::KISSAT) { // LCOV_EXCL_LINE
    // This exact fallback is reached after the cached-assumption query could
    // not answer.  Use the incremental-friendly backend so the local query has
    // both conflict and decision limits; Kissat can otherwise spend the wall in
    // propagation on a single residual Swerv leaf.
    return SATSolverWrapper::assumptionSolverTypeFor(configuredSolverType); // LCOV_EXCL_LINE
  }
  return configuredSolverType;
}

size_t dualRailResetBootstrapBmcTransitionSourceLimit();
size_t dualRailResetFrontierTransitionSourceLimit();
size_t dualRailResetFrontierStateSymbolLimit();

bool shouldUseExactResetFrontierChecks(const KInductionProblem& problem,
                                       bool requested) {
  if (!requested || !problem.usesDualRailStateEncoding) {
    return requested;
  }
  const size_t railStateSymbols = pdrDualRailStateSymbolCount(problem);
  const size_t originalOutputs = pdrOriginalObservedOutputCount(problem);
  // Keep the shared 129f390/376a017 guard: small output surfaces can use exact
  // reset-frontier directly, while medium output surfaces must also have a
  // large enough rail-state surface to amortize the exact frontier context.
  // This keeps AES-sized residual leaves on the lower-memory PDR path.
  const bool outputSurfaceAllowed =
      problem.observedOutputExprs0.size() <=
          kMaxExactResetFrontierDualRailObservedOutputs &&
      originalOutputs <= kMaxExactResetFrontierDualRailOriginalOutputs &&
      (originalOutputs <= kMaxExactResetFrontierDualRailSmallOriginalOutputs ||
       railStateSymbols >=
           kMinExactResetFrontierDualRailMediumStateSymbols);

  return railStateSymbols <= dualRailResetFrontierStateSymbolLimit() &&
         pdrTransitionSourceCount(problem) <=
             dualRailResetFrontierTransitionSourceLimit() &&
         outputSurfaceAllowed;
}

KEPLER_FORMAL::Config::SolverType badFormulaValidationSolverType(
    KEPLER_FORMAL::Config::SolverType solverType) {
  // The main PDR loop is tuned for Kissat's many short predecessor queries.
  // Whole-bad-formula validation is different: it is an optional exact BMC
  // LCOV_EXCL_START
  // repair over a wider frontier formula. BlackParrot samples showed a single
  // LCOV_EXCL_STOP
  // Kissat validation query dominating the run, while failure to validate just
  // means "fall back to normal PDR." Use CaDiCaL for this optional proof when
  // the selected solver is Kissat; UNSAT remains a real proof, SAT/UNKNOWN only
  // disables the shortcut.
  return solverType == KEPLER_FORMAL::Config::SolverType::KISSAT
             ? KEPLER_FORMAL::Config::SolverType::CADICAL
             : solverType;  // LCOV_EXCL_LINE
}

size_t envSizeLimitOrDefault(const char* name, size_t defaultValue);

KEPLER_FORMAL::Config::SolverType stateEqualitySubsetSolverType(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    size_t equalityPairCount,
    size_t solverSymbols) {
  constexpr size_t kMediumDualRailStateEqualityPairs = 64;
  constexpr size_t kMediumDualRailStateEqualitySymbols = 256;
  // This is still the selected PDR proof path. Only the local SAT backend for
  // the inductiveness-pruning query changes: medium dual-rail equality
  // surfaces are model-producing and much wider than normal predecessor
  // blocking queries, where Kissat remains the default.
  if (detail::pdrStateEqualitySubsetPrefersCadical(
          problem.usesDualRailStateEncoding,
          equalityPairCount,
          solverType,
          solverSymbols,
          kMediumDualRailStateEqualityPairs,
          kMediumDualRailStateEqualitySymbols)) {
    return KEPLER_FORMAL::Config::SolverType::CADICAL; // LCOV_EXCL_LINE
  }
  return solverType;
}

bool pdrResetShortcutDiagEnabled() {
  return std::getenv("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG") != nullptr;
}

std::string_view concreteCubeReachabilityModeName(
    // LCOV_EXCL_START
    ConcreteCubeReachabilityMode mode) {
    // LCOV_EXCL_STOP
  switch (mode) {
    case ConcreteCubeReachabilityMode::CachedAssumptions:
      return "cached_assumptions";
    case ConcreteCubeReachabilityMode::OneShotUnitClauses:
      return "one_shot_unit_clauses";
  }
  return "unknown";  // LCOV_EXCL_LINE
}

size_t pdrStatsInterval() {
  const char* intervalText = std::getenv("KEPLER_SEC_PDR_STATS_INTERVAL");
  if (intervalText == nullptr || *intervalText == '\0') {
    return kDefaultPdrStatsInterval;  // LCOV_EXCL_LINE
  }

  const auto interval = std::strtoull(intervalText, nullptr, 10);
  return interval == 0 ? 1 : static_cast<size_t>(interval);
}

size_t envSizeLimitOrDefault(const char* name, size_t defaultValue) {
  const char* valueText = std::getenv(name);
  if (valueText == nullptr || *valueText == '\0') {
    return defaultValue;
  }
  const auto value = std::strtoull(valueText, nullptr, 10);
  return value == 0 ? defaultValue : static_cast<size_t>(value);
}

unsigned envUnsignedLimitOrDefaultAllowZero(const char* name,
                                            // LCOV_EXCL_START
                                            unsigned defaultValue) {
                                            // LCOV_EXCL_STOP
  const char* valueText = std::getenv(name);
  if (valueText == nullptr || *valueText == '\0') {
    return defaultValue;
  }
  const auto value = std::strtoull(valueText, nullptr, 10);
  return value > std::numeric_limits<unsigned>::max()
             ? std::numeric_limits<unsigned>::max()  // LCOV_EXCL_LINE
             : static_cast<unsigned>(value);
}

unsigned resetExpressionProofConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT",
      kDefaultResetExpressionProofConflictLimit);
}

unsigned dualRailBadCubeConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_DUAL_RAIL_BAD_CUBE_CONFLICT_LIMIT",
      kDefaultDualRailBadCubeConflictLimit);
}

unsigned dualRailPredecessorConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      kDualRailPredecessorConflictLimitEnv,
      kDefaultDualRailPredecessorConflictLimit);
}

unsigned dualRailPredecessorConflictLimitForQuery(
    const KInductionProblem& problem,
    const StateCube& targetCube,
    size_t level,
    size_t solverSymbolCount) {
  const unsigned configuredLimit = dualRailPredecessorConflictLimit();
  if (std::getenv(kDualRailPredecessorConflictLimitEnv) != nullptr) {
    return configuredLimit; // LCOV_EXCL_LINE
  }
  // BlackParrot leaves with one residual output need a deeper predecessor SAT
  // search, but broad multi-output batches should keep the cheaper default.
  // Keep this scoped to small target cubes and local solver cones so it repairs
  // isolated handshake leaves without opening whole-SoC predecessor searches.
  if (detail::shouldUseResidualDualRailPredecessorBudget(
          problem.usesDualRailStateEncoding,
          problem.observedOutputExprs0.size(),
          level,
          targetCube.size(),
          solverSymbolCount)) {
    return std::max(
        configuredLimit,
        kDefaultDualRailResidualPredecessorConflictLimit);
  }
  return configuredLimit;
}

unsigned dualRailPredecessorDecisionLimit(unsigned defaultValue) {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_DECISION_LIMIT",
      defaultValue);
}

size_t dualRailPredecessorEncodingNodeLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_ENCODING_NODE_LIMIT",
      kDefaultDualRailPredecessorEncodingNodeLimit);
}

size_t dualRailPredecessorEncodingSupportLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_PREDECESSOR_ENCODING_SUPPORT_LIMIT",
      kDefaultDualRailPredecessorEncodingSupportLimit);
}

size_t dualRailResetBootstrapBmcTransitionSourceLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_RESET_BMC_TRANSITION_SOURCE_LIMIT",
      kMaxDualRailResetBootstrapBmcTransitionSources);
}

size_t dualRailResetFrontierTransitionSourceLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_RESET_FRONTIER_TRANSITION_SOURCE_LIMIT",
      kMaxExactResetFrontierDualRailTransitionSources);
}

size_t dualRailResetFrontierStateSymbolLimit() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_DUAL_RAIL_RESET_FRONTIER_STATE_SYMBOL_LIMIT",
      kMaxExactResetFrontierDualRailStateSymbols);
}

size_t maxProjectedFrameClausesPerQuery() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_CLAUSE_LIMIT",
      kDefaultMaxProjectedFrameClausesPerQuery);
}

size_t maxProjectedFrameLiteralsPerQuery() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_LITERAL_LIMIT",
      kDefaultMaxProjectedFrameLiteralsPerQuery);
}

size_t maxProjectedFrameRefinementsBeforeExactRetry() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_PROJECTED_FRAME_REFINEMENT_LIMIT",
      kDefaultMaxProjectedFrameRefinementsBeforeExactRetry);
}

size_t maxRepeatedProjectedBadCubeHits() {
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_REPEATED_PROJECTED_BAD_CUBE_LIMIT",
      kDefaultMaxRepeatedProjectedBadCubeHits);
}

size_t maxExactResetPrecheckTransitionSupport(
    KEPLER_FORMAL::Config::SolverType solverType) {
  const auto assumptionSolverType =
      SATSolverWrapper::assumptionSolverTypeFor(solverType);
  const size_t defaultLimit =
      assumptionSolverType == KEPLER_FORMAL::Config::SolverType::GLUCOSE
          ? kMaxGlucoseExactResetPrecheckTransitionSupport
          : kMaxCadicalExactResetPrecheckTransitionSupport;
  return envSizeLimitOrDefault(
      "KEPLER_SEC_PDR_EXACT_RESET_PRECHECK_SUPPORT_LIMIT", defaultLimit);
}

size_t nextPdrPredecessorQueryNumber() {
  // The stats path is intentionally process-local and diagnostic-only. PDR is
  // currently run serially per SEC output slice, so a simple counter gives a
  // stable view of where a long proof is spending time without touching the
  // proof algorithm or adding synchronization overhead to normal runs.
  static size_t queryNumber = 0;
  return ++queryNumber;
}

size_t nextPdrProjectedBlockedRetryNumber() {
  static size_t retryNumber = 0;
  return ++retryNumber;
}

size_t nextPdrDualRailPredecessorCoreSkipNumber() {
  static size_t skipNumber = 0;
  return ++skipNumber;
}

bool shouldEmitPdrStats(size_t queryNumber) {
  if (!pdrStatsEnabled()) {
    return false;
  }
  return queryNumber <= kInitialPdrStatsQueries ||
         queryNumber % pdrStatsInterval() == 0;
}

class PdrFormulaSupportCache {
 // LCOV_EXCL_START
 public:
 // LCOV_EXCL_STOP
  explicit PdrFormulaSupportCache(
      const std::vector<DualRailSymbolPair>& dualRailStatePairs) {
    dualRailPartnerBySymbol_.reserve(dualRailStatePairs.size() * 2);
    for (const auto& rails : dualRailStatePairs) {
      dualRailPartnerBySymbol_.emplace(rails.mayBeOne, rails.mayBeZero);
      dualRailPartnerBySymbol_.emplace(rails.mayBeZero, rails.mayBeOne);
    }
  }

  const std::set<size_t>& support(BoolExpr* formula) {
    static const std::set<size_t> emptySupport;
    if (formula == nullptr) {
      return emptySupport;  // LCOV_EXCL_LINE
    }
    if (const auto it = supportByExpr_.find(formula);
        it != supportByExpr_.end()) {
      return it->second;
    }
    const auto [it, _] =
        supportByExpr_.emplace(formula, formula->getSupportVars());
    return it->second;
  }

  void addRelevantDualRailPartners(std::unordered_set<size_t>& symbols) const {
    if (dualRailPartnerBySymbol_.empty() || symbols.empty()) {
      return;
    }
    std::vector<size_t> worklist =
        detail::makePdrClosureWorklist(symbols);
    for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
      const auto partnerIt = dualRailPartnerBySymbol_.find(worklist[cursor]);
      if (partnerIt == dualRailPartnerBySymbol_.end()) {
        continue;
      }
      if (symbols.insert(partnerIt->second).second) {
        worklist.push_back(partnerIt->second);
      }
    }
  }

  size_t clearMemoizedSupports() {
    const size_t entries = supportByExpr_.size();
    supportByExpr_.clear();
    supportByExpr_.rehash(0);
    return entries;
  }

 private:
  // PDR rebuilds many local SAT queries over the same frame/property formulas.
  // Memoizing formula support avoids repeatedly walking large BoolExpr DAGs
  // while keeping each query's selected symbol set unchanged.
  std::unordered_map<BoolExpr*, std::set<size_t>> supportByExpr_;
  std::unordered_map<size_t, size_t> dualRailPartnerBySymbol_;
};

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames);

void addSameFrameStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t numFrames);

void addDualRailStateValidity(SATSolverWrapper& solver,
                              const FrameVariableStore& variables,
                              const std::vector<DualRailSymbolPair>& railPairs,
                              size_t numFrames);

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame);

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame);

StateClause clauseFromCube(const StateCube& cube);

std::vector<size_t> cubeStateSymbols(const StateCube& cube);

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame);

void addFormulaSymbols(BoolExpr* formula,
                       std::unordered_set<size_t>& symbols,
                       PdrFormulaSupportCache* supportCache = nullptr);

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output,
                            PdrFormulaSupportCache& supportCache);

bool predecessorSourceFrameIsKnownSafe(size_t level);

void normalizeCube(StateCube& cube);

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols);

bool cubeOutsideConcreteResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    bool useResetConstantShortcut = true,
    ConcreteCubeReachabilityMode mode =
        ConcreteCubeReachabilityMode::CachedAssumptions,
    BoolExpr* frameInvariant = nullptr,
    bool resourceLimitStartupExactQuery = false);

bool cubeReachableWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode =
        ConcreteCubeReachabilityMode::CachedAssumptions,
    BoolExpr* frameInvariant = nullptr);

bool cubeReachableAtConcreteFrame(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode,
    BoolExpr* frameInvariant,
    bool usePostBootstrapPrechecks = true);

bool cubeOutsideConcreteFrameByCheapResetFacts(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant,
    bool allowLargeDualRailSmallCubeBudget = false);

ResetFrontierReachabilityContext& resetReachabilityContextFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant);

// LCOV_EXCL_START
std::vector<size_t> sortUniqueSymbols(std::unordered_set<size_t> symbols) {
// LCOV_EXCL_STOP
  std::vector<size_t> ordered(symbols.begin(), symbols.end());
  std::sort(ordered.begin(), ordered.end());
  ordered.erase(std::unique(ordered.begin(), ordered.end()), ordered.end());
  return ordered;
}

std::optional<std::vector<size_t>> collectBoundedStateSupportSymbols(
    BoolExpr* formula,
    size_t maxVisitedNodes,
    size_t maxStateSymbols,
    const std::unordered_set<size_t>& stateSymbolSet) {
  if (formula == nullptr) {
    // LCOV_EXCL_START
    return {};  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  std::unordered_set<size_t> stateSupport;
  std::unordered_set<const BoolExpr*> visited;
  std::vector<const BoolExpr*> stack{formula};
  while (!stack.empty()) {
    const BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;  // LCOV_EXCL_LINE
    }
    if (visited.size() > maxVisitedNodes) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (node->getOp() == Op::VAR) {
      if (stateSymbolSet.find(node->getId()) != stateSymbolSet.end()) {
        stateSupport.insert(node->getId());
        if (stateSupport.size() > maxStateSymbols) {
          return std::nullopt;
        }
      }
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return sortUniqueSymbols(std::move(stateSupport));
}

std::vector<size_t> collectStateSupportPrefixSymbols(
    BoolExpr* formula,
    size_t maxVisitedNodes,
    size_t maxStateSymbols,
    const std::unordered_set<size_t>& stateSymbolSet) {
  if (formula == nullptr || maxStateSymbols == 0) {
    return {}; // LCOV_EXCL_LINE
  }

  std::unordered_set<size_t> seenStateSupport;
  std::vector<size_t> stateSupport;
  std::unordered_set<const BoolExpr*> visited;
  std::vector<const BoolExpr*> stack{formula};
  while (!stack.empty() && stateSupport.size() < maxStateSymbols) {
    const BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;  // LCOV_EXCL_LINE
    }
    if (visited.size() > maxVisitedNodes) {
      break;  // LCOV_EXCL_LINE
    }
    if (node->getOp() == Op::VAR) {
      if (stateSymbolSet.find(node->getId()) != stateSymbolSet.end() &&
          seenStateSupport.insert(node->getId()).second) {
        stateSupport.push_back(node->getId());
      }
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  std::sort(stateSupport.begin(), stateSupport.end());
  return stateSupport;
}

// LCOV_EXCL_START
std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  // LCOV_EXCL_STOP
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      targets.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      targets.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> collectTransitionSupportSymbols(
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    const std::vector<size_t>& encodedTargets) {
    // LCOV_EXCL_STOP
  std::unordered_set<size_t> supportSymbols;
  for (const auto stateSymbol : encodedTargets) {
    const auto& support = transitionByState.support(stateSymbol);
    supportSymbols.insert(support.begin(), support.end());
  }
  return sortUniqueSymbols(std::move(supportSymbols));
}

size_t estimateTransitionEncodingNodes(
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& encodedTargets) {
  if (encodedTargets.size() > kMaxExactTransitionNodeCountHintTargets) {
    return 0;  // LCOV_EXCL_LINE
  }
  size_t estimate = 0;
  for (const auto stateSymbol : encodedTargets) {
    estimate += transitionByState.nodeCount(stateSymbol);
  }
  return estimate;
}

PredecessorTargetSurface buildPredecessorTargetSurface(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  PredecessorTargetSurface surface;
  surface.targetSymbols = cubeStateSymbols(targetCube);
  surface.encodedTargets =
      expandTransitionTargets(problem, surface.targetSymbols, transitionByState);
  surface.transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, surface.encodedTargets);
  surface.transitionEncodingNodes =
      estimateTransitionEncodingNodes(transitionByState, surface.encodedTargets);
  return surface;
}

const PredecessorTargetSurface& predecessorTargetSurfaceFor(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  PredecessorTargetSurfaceKey key{&problem, &transitionByState, targetCube};
  const auto existing = cache.targetSurfaces.find(key);
  if (existing != cache.targetSurfaces.end()) {
    return existing->second;
  }
  if (cache.targetSurfaces.size() >=
      kMaxPredecessorTargetSurfaceCacheEntries) {
    // These vectors are pure target-derived data. Clearing the bounded cache
    // only gives up reuse; it cannot change a predecessor answer.
    cache.targetSurfaces.clear(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  PredecessorTargetSurface surface =
      buildPredecessorTargetSurface(problem, transitionByState, targetCube);
  auto [inserted, insertedNew] =
      cache.targetSurfaces.emplace(std::move(key), std::move(surface));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor target surface cached target=",
        targetCube.size(),
        " encoded_targets=",
        inserted->second.encodedTargets.size(),
        " transition_support=",
        inserted->second.transitionSupportSymbols.size(),
        " entries=",
        cache.targetSurfaces.size());
  }
  return inserted->second;
}

struct TransitionEncodingGroup {
  const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
  std::vector<size_t> stateSymbols;
};

void appendTransitionEncodingGroup(
    std::vector<TransitionEncodingGroup>& groups,
    const std::unordered_map<size_t, size_t>* symbolMap,
    size_t stateSymbol) {
  for (auto& group : groups) {
    if (group.symbolMap == symbolMap) {
      group.stateSymbols.push_back(stateSymbol);
      return;
    }
  }
  groups.push_back(TransitionEncodingGroup{symbolMap, {stateSymbol}});
}

std::vector<TransitionEncodingGroup> groupTransitionTargetsBySymbolMap(
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& encodedTargets) {
  std::vector<TransitionEncodingGroup> groups;
  groups.reserve(3);
  for (const auto stateSymbol : encodedTargets) {
    const TransitionExprView view = transitionByState.expressionView(stateSymbol);
    appendTransitionEncodingGroup(groups, view.symbolMap, stateSymbol);
  }
  for (auto& group : groups) {
    std::sort(group.stateSymbols.begin(), group.stateSymbols.end());
    group.stateSymbols.erase(
        std::unique(group.stateSymbols.begin(), group.stateSymbols.end()),
        group.stateSymbols.end());
  }
  return groups;
}

struct TransitionEncodingLiteral {
  size_t transitionSymbol = 0;
  bool desiredValue = false;
  CubeLiteral originalLiteral;
};

struct TransitionEncodingLiteralGroup {
  const std::unordered_map<size_t, size_t>* symbolMap = nullptr;
  std::vector<TransitionEncodingLiteral> literals;
  std::vector<size_t> stateSymbols;
};

void appendTransitionEncodingLiteralGroup(
    std::vector<TransitionEncodingLiteralGroup>& groups,
    const std::unordered_map<size_t, size_t>* symbolMap,
    TransitionEncodingLiteral literal) {
  for (auto& group : groups) {
    if (group.symbolMap == symbolMap) {
      group.stateSymbols.push_back(literal.transitionSymbol);
      group.literals.push_back(std::move(literal));
      return;
    }
  }
  TransitionEncodingLiteralGroup group;
  group.symbolMap = symbolMap;
  group.stateSymbols.push_back(literal.transitionSymbol);
  group.literals.push_back(std::move(literal));
  // LCOV_EXCL_START
  groups.push_back(std::move(group));
}

std::vector<TransitionEncodingLiteralGroup> groupTransitionCubeLiteralsBySymbolMap(
// LCOV_EXCL_STOP
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    const StateCube& targetCube) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::vector<TransitionEncodingLiteralGroup> groups;
  // LCOV_EXCL_STOP
  groups.reserve(3);
  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);  // LCOV_EXCL_LINE
      if (primaryIt == primaryByComplement.end() ||  // LCOV_EXCL_LINE
          !transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      transitionSymbol = primaryIt->second;  // LCOV_EXCL_LINE
      desiredValue = !desiredValue;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    const TransitionExprView view =
        transitionByState.expressionView(transitionSymbol);
    appendTransitionEncodingLiteralGroup(
        groups,
        view.symbolMap,
        TransitionEncodingLiteral{transitionSymbol, desiredValue, literal});
  }
  for (auto& group : groups) {
    std::sort(group.stateSymbols.begin(), group.stateSymbols.end());
    group.stateSymbols.erase(
        std::unique(group.stateSymbols.begin(), group.stateSymbols.end()),
        group.stateSymbols.end());
  }
  return groups;
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
std::vector<size_t> cubeStateSymbols(const StateCube& cube) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
std::vector<size_t> boundedPrefixSymbols(const std::vector<size_t>& symbols,
                                         size_t limit) {
  if (limit == 0 || symbols.size() <= limit) {
    return symbols;  // LCOV_EXCL_LINE
  }
  return std::vector<size_t>(symbols.begin(), symbols.begin() + limit);
// LCOV_EXCL_START
}

StateCube boundedPrefixCube(const StateCube& cube, size_t limit) {
  if (limit == 0 || cube.size() <= limit) {
  // LCOV_EXCL_STOP
    return cube;
  // LCOV_EXCL_START
  }
  return StateCube(cube.begin(), cube.begin() + limit);  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
}

bool shouldAvoidTransitionNodeCountCost(const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding &&
         (pdrDualRailStateSymbolCount(problem) >
              dualRailResetFrontierStateSymbolLimit() ||
          pdrTransitionSourceCount(problem) > // LCOV_EXCL_LINE
              dualRailResetFrontierTransitionSourceLimit() || // LCOV_EXCL_LINE
          pdrOriginalObservedOutputCount(problem) > // LCOV_EXCL_LINE
              kMaxExactResetFrontierDualRailOriginalOutputs);
}

size_t transitionLiteralCost(const KInductionProblem& problem,
                             const TransitionExprResolver& transitionByState,
                             size_t symbol) {
  size_t transitionSymbol = symbol;
  if (!transitionByState.contains(transitionSymbol)) {
    const auto primaryIt = transitionByState.primaryByComplement().find(symbol);  // LCOV_EXCL_LINE
    if (primaryIt == transitionByState.primaryByComplement().end() ||  // LCOV_EXCL_LINE
        !transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
      return 0;  // LCOV_EXCL_LINE
    }
    transitionSymbol = primaryIt->second;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  // Support width is the dominant SAT-query cost; node count breaks ties among
  // cones with similar state/input footprints. On large lazy dual-rail
  // surfaces, nodeCount() materializes the lifted transition DAG just to order
  // optional PDR probes. Use support-only ordering there so the heuristic does
  // not fill the shared dual-rail remap memo before the exact query starts.
  const size_t supportCost = transitionByState.support(transitionSymbol).size() * 4;
  if (shouldAvoidTransitionNodeCountCost(problem)) {
    return supportCost;
  }
  return supportCost + transitionByState.nodeCount(transitionSymbol);
}

size_t blockedCubeTransitionSupportSize(
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_STOP
    const StateCube& cube) {
  const std::vector<size_t> targetSymbols = cubeStateSymbols(cube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  return collectTransitionSupportSymbols(transitionByState, encodedTargets).size();
}

size_t effectivePreciseBadCubeStateLimit(const KInductionProblem& problem,
                                         size_t configuredLimit,
                                         bool useExactResetFrontierChecks) {
  if (problem.usesDualRailStateEncoding &&
      problem.resetBootstrapCycles != 0 &&
      useExactResetFrontierChecks) {
    // Exact reset-frontier PDR immediately minimizes and learns sibling
    // singleton blockers. A slightly wider bad cube lets one reset SAT query
    // cover a whole local bus slice instead of rediscovering it four bits at a
    // time, while leaving non-reset and binary PDR behavior unchanged.
    return std::max(
        configuredLimit, kMaxExactResetPredecessorBadCubeLimit);
  }
  return configuredLimit;
}

StateCube boundedCheapTransitionCube(
    const StateCube& cube,
    size_t limit,
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState) {
    // LCOV_EXCL_STOP
  if (limit == 0 || cube.size() <= limit) {
    return cube;  // LCOV_EXCL_LINE
  }

  StateCube selected = cube;
  std::stable_sort(
      selected.begin(),
      selected.end(),
      [&](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        const size_t lhsCost =
            transitionLiteralCost(problem, transitionByState, lhs.symbol);
        const size_t rhsCost =
            transitionLiteralCost(problem, transitionByState, rhs.symbol);
        if (lhsCost != rhsCost) {
          return lhsCost < rhsCost;  // LCOV_EXCL_LINE
        }
        return lhs.symbol < rhs.symbol;
      });
  selected.resize(limit);
  normalizeCube(selected);
  return selected;
}

std::vector<std::pair<size_t, bool>> cubeAssignments(const StateCube& cube) {
  std::vector<std::pair<size_t, bool>> assignments;
  assignments.reserve(cube.size());
  for (const auto& literal : cube) {
    assignments.emplace_back(literal.symbol, literal.value);
  }
  return assignments;
}

StateCube cubeFromAssignments(
    const std::vector<std::pair<size_t, bool>>& assignments) {
  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

bool cubeContainsCube(const StateCube& cube, const StateCube& core) {
  return std::includes(
      cube.begin(),
      cube.end(),
      core.begin(),
      core.end(),
      [](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        if (lhs.symbol != rhs.symbol) {
          return lhs.symbol < rhs.symbol;
        }
        // LCOV_EXCL_START
        return lhs.value < rhs.value;
        // LCOV_EXCL_STOP
      });
}

ResetFrontierCubeKey resetFrontierCacheKey(const StateCube& cube,
                                           size_t postBootstrapSteps);

bool rememberResetUnreachableCoreInVector(std::vector<StateCube>& cores,
                                          StateCube core) {
  normalizeCube(core);
  if (core.empty()) {
    return false;  // LCOV_EXCL_LINE
  }

  for (const auto& existing : cores) {
    if (cubeContainsCube(core, existing)) {
      return false; // LCOV_EXCL_LINE
    }
  }
  for (auto it = cores.begin(); it != cores.end();) {
    if (cubeContainsCube(*it, core)) {
      it = cores.erase(it);
      continue;
    }
    ++it;
  }
  cores.push_back(std::move(core));
  sortStateCubesDeterministically(cores);
  if (cores.size() > kMaxPdrResetUnreachableCoresPerStep) {
    cores.pop_back();  // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return true;
}

// LCOV_EXCL_START
void rememberPdrResetUnreachableCore(
// LCOV_EXCL_STOP
    ResetFrontierCache& cache,
    StateCube core,
    size_t postBootstrapSteps) {
  auto& cores =
      cache.resetUnreachableCoresByPostBootstrapStep[postBootstrapSteps];
  (void)rememberResetUnreachableCoreInVector(cores, std::move(core));
}


// LCOV_DISABLED_STOP
void rememberTransitionImpossibleResetCore(  // LCOV_EXCL_LINE
    ResetFrontierCache& cache,
    // LCOV_EXCL_START
    StateCube core) {
  normalizeCube(core);  // LCOV_EXCL_LINE
  if (core.empty()) {  // LCOV_EXCL_LINE
    return;  // LCOV_EXCL_LINE
  }


// LCOV_EXCL_STOP
  const StateCube key = resetFrontierCacheKey(core, 0).cube;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  cache.transitionImpossibleResetCoreByKey[key] = true;  // LCOV_EXCL_LINE
  for (const auto& existing : cache.transitionImpossibleResetCores) {  // LCOV_EXCL_LINE
    if (cubeContainsCube(core, existing)) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      return;  // LCOV_EXCL_LINE
    }
  }
  cache.transitionImpossibleResetCores.erase(  // LCOV_EXCL_LINE
      std::remove_if(  // LCOV_EXCL_LINE
          cache.transitionImpossibleResetCores.begin(),  // LCOV_EXCL_LINE
          cache.transitionImpossibleResetCores.end(),  // LCOV_EXCL_LINE
          [&](const StateCube& existing) {  // LCOV_EXCL_LINE
            return cubeContainsCube(existing, core);  // LCOV_EXCL_LINE
          }),
      cache.transitionImpossibleResetCores.end());  // LCOV_EXCL_LINE
  cache.transitionImpossibleResetCores.push_back(std::move(core));  // LCOV_EXCL_LINE
  sortStateCubesDeterministically(cache.transitionImpossibleResetCores);  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> findPdrResetUnreachableCoreForCube(
    const ResetFrontierCache& cache,
    const StateCube& cube,
    size_t postBootstrapSteps) {
  const auto it =
      cache.resetUnreachableCoresByPostBootstrapStep.find(postBootstrapSteps);
  if (it == cache.resetUnreachableCoresByPostBootstrapStep.end()) {
    return std::nullopt;
  }
  for (const auto& core : it->second) {
    if (cubeContainsCube(cube, core)) {
      return core;
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return std::nullopt;
}

std::vector<StateCube> findPdrResetUnreachableSingletonCoresForCube(
    const ResetFrontierCache& cache,
    const StateCube& cube,
    size_t postBootstrapSteps) {
  std::vector<StateCube> cores;
  const auto it =
      cache.resetUnreachableCoresByPostBootstrapStep.find(postBootstrapSteps);
  if (it == cache.resetUnreachableCoresByPostBootstrapStep.end()) {
    return cores;
  }

  for (const auto& core : it->second) {
    if (core.size() == 1 && cubeContainsCube(cube, core)) {
      cores.push_back(core);
    }
  }
  sortStateCubesDeterministically(cores);
  return cores;
}

struct ProcessResetUnreachableCoreCacheKey { // LCOV_EXCL_LINE
  const LazyTransitionStore* lazyTransitions = nullptr; // LCOV_EXCL_LINE
  size_t resetBootstrapCycles = 0; // LCOV_EXCL_LINE
  size_t state0Symbols = 0; // LCOV_EXCL_LINE
  size_t state1Symbols = 0; // LCOV_EXCL_LINE
  size_t transitions0 = 0; // LCOV_EXCL_LINE
  size_t transitions1 = 0; // LCOV_EXCL_LINE

  bool operator==(const ProcessResetUnreachableCoreCacheKey& other) const { // LCOV_EXCL_LINE
    return lazyTransitions == other.lazyTransitions && // LCOV_EXCL_LINE
           resetBootstrapCycles == other.resetBootstrapCycles && // LCOV_EXCL_LINE
           state0Symbols == other.state0Symbols && // LCOV_EXCL_LINE
           state1Symbols == other.state1Symbols && // LCOV_EXCL_LINE
           transitions0 == other.transitions0 && // LCOV_EXCL_LINE
           transitions1 == other.transitions1; // LCOV_EXCL_LINE
  }
};

struct ProcessResetUnreachableCoreCacheEntry { // LCOV_EXCL_LINE
  ProcessResetUnreachableCoreCacheKey key;
  std::unordered_map<size_t, std::vector<StateCube>>
      coresByPostBootstrapStep;
};

std::vector<ProcessResetUnreachableCoreCacheEntry>&
processResetUnreachableCoreCache() {
  static std::vector<ProcessResetUnreachableCoreCacheEntry> cache;
  return cache;
}

ProcessResetUnreachableCoreCacheKey processResetUnreachableCoreCacheKey(
    const KInductionProblem& problem) {
  return {
      problem.lazyTransitions.get(),
      problem.resetBootstrapCycles,
      problem.state0Symbols.size(),
      problem.state1Symbols.size(),
      problem.transitions0.size(),
      problem.transitions1.size()};
}

bool canUseProcessResetUnreachableCoreCache(
    const KInductionProblem& problem,
    BoolExpr* frameInvariant) {
  // The cached cores are concrete reset-frontier facts.  Do not share cores
  // learned under an extra PDR frame invariant; that invariant may be local to
  // one proof slice even when the reset/transition system is otherwise shared.
  return frameInvariant == nullptr &&
         problem.usesDualRailStateEncoding &&
         problem.lazyTransitions != nullptr &&
         problem.resetBootstrapCycles != 0 &&
         (hasLocalDualRailFinalLeafRepairSurface(problem) ||
          hasLargeDualRailResetFrontierSurface(problem));
}

ProcessResetUnreachableCoreCacheEntry*
findProcessResetUnreachableCoreCacheEntry(
    const ProcessResetUnreachableCoreCacheKey& key) {
  auto& cache = processResetUnreachableCoreCache();
  for (auto& entry : cache) {
    if (entry.key == key) { // LCOV_EXCL_LINE
      return &entry; // LCOV_EXCL_LINE
    }
  }
  return nullptr;
}

void importProcessResetUnreachableCores(
    const KInductionProblem& problem,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (!canUseProcessResetUnreachableCoreCache(problem, frameInvariant)) {
    return;
  }
  const auto key = processResetUnreachableCoreCacheKey(problem);
  const auto* entry = findProcessResetUnreachableCoreCacheEntry(key);
  if (entry == nullptr) {
    return;
  }

  size_t imported = 0; // LCOV_EXCL_LINE
  for (const auto& [postBootstrapSteps, cores] : // LCOV_EXCL_LINE
       entry->coresByPostBootstrapStep) { // LCOV_EXCL_LINE
    for (const auto& core : cores) { // LCOV_EXCL_LINE
      if (findPdrResetUnreachableCoreForCube( // LCOV_EXCL_LINE
              cache, core, postBootstrapSteps) // LCOV_EXCL_LINE
          .has_value()) { // LCOV_EXCL_LINE
        continue; // LCOV_EXCL_LINE
      }
      rememberPdrResetUnreachableCore(cache, core, postBootstrapSteps); // LCOV_EXCL_LINE
      cache.outsideByCubeKey.emplace( // LCOV_EXCL_LINE
          resetFrontierCacheKey(core, postBootstrapSteps), true); // LCOV_EXCL_LINE
      ++imported; // LCOV_EXCL_LINE
    }
  }
  if (imported != 0 && pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: imported process reset-predecessor cores ",
        "cores=", imported,
        " steps=", entry->coresByPostBootstrapStep.size()); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
}

void rememberProcessResetUnreachableCores(
    const KInductionProblem& problem,
    const ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (!canUseProcessResetUnreachableCoreCache(problem, frameInvariant) ||
      cache.resetUnreachableCoresByPostBootstrapStep.empty()) {
    return;
  }
  const auto key = processResetUnreachableCoreCacheKey(problem); // LCOV_EXCL_LINE
  auto& processCache = processResetUnreachableCoreCache(); // LCOV_EXCL_LINE
  ProcessResetUnreachableCoreCacheEntry* entry = // LCOV_EXCL_LINE
      findProcessResetUnreachableCoreCacheEntry(key); // LCOV_EXCL_LINE
  if (entry == nullptr) { // LCOV_EXCL_LINE
    if (processCache.size() >= kMaxProcessResetUnreachableCoreCacheEntries) { // LCOV_EXCL_LINE
      processCache.erase(processCache.begin()); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    ProcessResetUnreachableCoreCacheEntry nextEntry; // LCOV_EXCL_LINE
    nextEntry.key = key; // LCOV_EXCL_LINE
    processCache.push_back(std::move(nextEntry)); // LCOV_EXCL_LINE
    entry = &processCache.back(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE

  size_t added = 0; // LCOV_EXCL_LINE
  size_t total = 0; // LCOV_EXCL_LINE
  for (const auto& [postBootstrapSteps, cores] : // LCOV_EXCL_LINE
       cache.resetUnreachableCoresByPostBootstrapStep) { // LCOV_EXCL_LINE
    auto& retained = entry->coresByPostBootstrapStep[postBootstrapSteps]; // LCOV_EXCL_LINE
    for (const auto& core : cores) { // LCOV_EXCL_LINE
      if (rememberResetUnreachableCoreInVector(retained, core)) { // LCOV_EXCL_LINE
        ++added; // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE
    }
  }
  for (const auto& [postBootstrapSteps, cores] : // LCOV_EXCL_LINE
       entry->coresByPostBootstrapStep) { // LCOV_EXCL_LINE
    (void)postBootstrapSteps; // LCOV_EXCL_LINE
    total += cores.size(); // LCOV_EXCL_LINE
  }
  if (added != 0 && pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: remembered process reset-predecessor cores ",
        "added=", added,
        " total=", total,
        " entries=", processCache.size()); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
}

void rememberPdrAndResetFrontierUnreachableCore(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    StateCube core,
    size_t postBootstrapSteps,
    BoolExpr* frameInvariant) {
  normalizeCube(core);
  if (core.empty()) {
    return;  // LCOV_EXCL_LINE
  }

// LCOV_EXCL_START

  rememberPdrResetUnreachableCore(cache, core, postBootstrapSteps);
  // LCOV_EXCL_STOP
  auto& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  rememberResetFrontierUnreachableCube(
      reachabilityContext, cubeAssignments(core), postBootstrapSteps);
}

StateCube minimizeExactResetPredecessorCore(
    const ResetFrontierReachabilityContext& reachabilityContext,
    KEPLER_FORMAL::Config::SolverType solverType,
    StateCube core,
    size_t postBootstrapSteps) {
  normalizeCube(core);
  if (core.size() <= 1) {
    return core;
  }

  size_t checks = 0;
  for (size_t index = 0;
       index < core.size() &&
       checks < kMaxExactResetPredecessorCoreDeletionChecks;) {
    StateCube trial = core;
    trial.erase(trial.begin() + static_cast<std::ptrdiff_t>(index));
    if (trial.empty()) {
      ++index;
      continue;
    }

    ++checks;
    // The first post-bootstrap reset precheck may have used a relaxed UNSAT
    // shortcut and cached the whole cube. Re-check smaller cubes against the
    // exact assumption-capable reset frontier before learning a stronger PDR
    // blocker.
    const bool reachable = isStateCubeReachableAtResetFrontier(
        reachabilityContext,
        solverType,
        cubeAssignments(trial),
        postBootstrapSteps,
        /*usePostBootstrapPrechecks=*/false);
    if (reachable) {
      ++index;
      continue;
    }

    if (const auto minimizedCore = findResetFrontierUnreachableCubeCore(
            reachabilityContext,
            solverType,
            cubeAssignments(trial),
            postBootstrapSteps);
        minimizedCore.has_value()) {
      StateCube nextCore = cubeFromAssignments(*minimizedCore);
      if (!nextCore.empty() && nextCore.size() <= trial.size()) {
        core = std::move(nextCore);
        index = 0;
        continue;
      }
    }

    core = std::move(trial); // LCOV_EXCL_LINE
    index = 0; // LCOV_EXCL_LINE
  }
  return core;
}

size_t seedExactResetPredecessorSiblingCores(
    ResetFrontierCache& cache,
    const ResetFrontierReachabilityContext& reachabilityContext,
    KEPLER_FORMAL::Config::SolverType solverType,
    const StateCube& cube,
    const StateCube& knownCore,
    size_t postBootstrapSteps) {
  if (!detail::shouldSeedExactResetPredecessorSiblingCores(
          cube.size(), knownCore.size())) {
    return 0;
  }

  size_t checks = 0;
  size_t seeded = 0;
  for (const auto& literal : cube) {
    if (checks >= kMaxExactResetPredecessorSiblingCoreChecks) {
      break; // LCOV_EXCL_LINE
    }
    StateCube siblingCore{literal};
    normalizeCube(siblingCore);
    if (cubeContainsCube(knownCore, siblingCore) ||
        findPdrResetUnreachableCoreForCube(
            cache, siblingCore, postBootstrapSteps)
            .has_value()) {
      continue;
    }

    ++checks;
    // Small projected reset-predecessor cubes often carry several independent
    // rail literals from the same bus slice. Proving those singleton siblings
    // now reuses the exact reset-frontier solver and avoids rediscovering the
    // same family as separate PDR bad cubes.
    const bool reachable = isStateCubeReachableAtResetFrontier(
        reachabilityContext,
        solverType,
        cubeAssignments(siblingCore),
        postBootstrapSteps,
        /*usePostBootstrapPrechecks=*/false);
    if (!reachable) {
      // This exact singleton proof is useful to both reset-frontier callers:
      // PDR checks the core list, while concrete reachability checks first
      // consult the exact cube-answer map and the reachability context.
      const auto siblingAssignments = cubeAssignments(siblingCore);
      rememberResetFrontierUnreachableCube(
          reachabilityContext, siblingAssignments, postBootstrapSteps);
      cache.outsideByCubeKey.emplace(
          resetFrontierCacheKey(siblingCore, postBootstrapSteps), true);
      rememberPdrResetUnreachableCore(
          cache, std::move(siblingCore), postBootstrapSteps);
      ++seeded;
    }
  }
  return seeded;
}

std::optional<StateCube> findTransitionImpossibleResetCoreForCube(
    const ResetFrontierCache& cache,
    const StateCube& cube) {
  for (const auto& core : cache.transitionImpossibleResetCores) {
    if (cubeContainsCube(cube, core)) {  // LCOV_EXCL_LINE
      return core;  // LCOV_EXCL_LINE
    }
  }
  return std::nullopt;
}

ResetFrontierCubeKey resetFrontierCacheKey(const StateCube& cube,
                                           size_t postBootstrapSteps) {
  // Several PDR paths derive equivalent root cubes from different obligation
  // sources. Canonicalize here so exact reset-frontier answers are reusable
  // even if a caller hands us the same literals in a different order.
  ResetFrontierCubeKey key;
  key.postBootstrapSteps = postBootstrapSteps;
  key.cube = cube;
  normalizeCube(key.cube);
  // LCOV_EXCL_START
  return key;
  // LCOV_EXCL_STOP
}

// LCOV_EXCL_START
ResetExpressionConflictKey resetExpressionConflictCacheKey(
// LCOV_EXCL_STOP
    const StateCube& cube,
    size_t targetStep,
    // LCOV_EXCL_START
    BoolExpr* frameInvariant) {
    // LCOV_EXCL_STOP
  ResetExpressionConflictKey key;
  key.frontier = resetFrontierCacheKey(cube, targetStep);
  key.frameInvariant = frameInvariant;
  return key;
}

// LCOV_EXCL_START

ResetFrontierCubeKey resetExpressionBudgetSkipKey(const StateCube& cube,
                                                  BoolExpr* frameInvariant) {
                                                  // LCOV_EXCL_STOP
  (void)frameInvariant;
  // LCOV_EXCL_START
  return resetFrontierCacheKey(cube, 0);
  // LCOV_EXCL_STOP
}

bool resetExpressionBudgetSkipApplies(  // LCOV_EXCL_LINE
    const std::unordered_map<ResetFrontierCubeKey, size_t, ResetFrontierCubeKeyHash>& skipFromStep,
    // LCOV_EXCL_START
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant) {
  const auto it =
      skipFromStep.find(resetExpressionBudgetSkipKey(cube, frameInvariant));
  return it != skipFromStep.end() && it->second <= targetStep;
  // LCOV_EXCL_STOP
}  // LCOV_EXCL_LINE

void rememberResetExpressionBudgetSkip(  // LCOV_EXCL_LINE
    std::unordered_map<ResetFrontierCubeKey, size_t, ResetFrontierCubeKeyHash>& skipFromStep,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant) {
  const ResetFrontierCubeKey key = resetExpressionBudgetSkipKey(cube, frameInvariant);  // LCOV_EXCL_LINE
  const auto [it, inserted] = skipFromStep.emplace(key, targetStep);  // LCOV_EXCL_LINE
  if (!inserted && targetStep < it->second) {  // LCOV_EXCL_LINE
    it->second = targetStep;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

const ResetExpressionConflictMemoEntry* lookupResetExpressionConflictMemo(
    const std::unordered_map<
        ResetExpressionConflictKey,
        ResetExpressionConflictMemoEntry,
        ResetExpressionConflictKeyHash>& memo,
    const ResetExpressionConflictKey& key) {
  const auto it = memo.find(key);
  if (it == memo.end()) {
    return nullptr;
  }
  return &it->second;
}

void rememberResetExpressionConflictMemo(
    std::unordered_map<
        ResetExpressionConflictKey,
        ResetExpressionConflictMemoEntry,
        ResetExpressionConflictKeyHash>& memo,
    const ResetExpressionConflictKey& key,
    const std::optional<StateCube>& conflict) {
  ResetExpressionConflictMemoEntry entry;
  entry.hasConflict = conflict.has_value();
  if (conflict.has_value()) {
    entry.conflict = *conflict;
  }
  memo[key] = std::move(entry);
}

uint64_t cubeFingerprint(const StateCube& cube) {
  uint64_t hash = 1469598103934665603ULL;
  for (const auto& literal : cube) {
    hash ^= static_cast<uint64_t>(literal.symbol) + 0x9e3779b97f4a7c15ULL;
    hash *= 1099511628211ULL;
    hash ^= literal.value ? 0xa5a5a5a5a5a5a5a5ULL : 0x5a5a5a5a5a5a5a5aULL;
    hash *= 1099511628211ULL;
  }
  return hash;
}

// LCOV_EXCL_START
std::string formatCubeForDiag(const StateCube& cube) {
  std::ostringstream oss;
  oss << "{";
  // LCOV_EXCL_STOP
  for (size_t i = 0; i < cube.size(); ++i) {
    // LCOV_EXCL_START
    if (i != 0) {
      oss << ",";
    }
    // LCOV_EXCL_STOP
    oss << cube[i].symbol << "=" << (cube[i].value ? "1" : "0");
  // LCOV_EXCL_START
  }
  oss << "}";
  return oss.str();
}

std::optional<SymbolPair> simpleVariableEqualityPair(BoolExpr* expr) {  // LCOV_EXCL_LINE
  if (expr == nullptr || expr->getOp() != Op::NOT) {  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  BoolExpr* xorExpr = expr->getLeft();  // LCOV_EXCL_LINE
  if (xorExpr == nullptr || xorExpr->getOp() != Op::XOR) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  BoolExpr* lhs = xorExpr->getLeft();  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  BoolExpr* rhs = xorExpr->getRight();  // LCOV_EXCL_LINE
  if (lhs == nullptr || rhs == nullptr ||  // LCOV_EXCL_LINE
      lhs->getOp() != Op::VAR || rhs->getOp() != Op::VAR ||  // LCOV_EXCL_LINE
      lhs->getId() < 2 || rhs->getId() < 2 ||  // LCOV_EXCL_LINE
      lhs->getId() == rhs->getId()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  SymbolPair pair{lhs->getId(), rhs->getId()};  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (pair.second < pair.first) {  // LCOV_EXCL_LINE
    std::swap(pair.first, pair.second);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return pair;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::vector<std::pair<size_t, size_t>> collectSimpleVariableEqualities(
// LCOV_EXCL_STOP
    BoolExpr* formula) {
  // LCOV_EXCL_START
  std::vector<std::pair<size_t, size_t>> equalities;
  if (formula == nullptr) {
    return equalities;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  std::unordered_set<SymbolPair, SymbolPairHash> seen;  // LCOV_EXCL_LINE
  std::vector<BoolExpr*> stack{formula};  // LCOV_EXCL_LINE
  while (!stack.empty()) {  // LCOV_EXCL_LINE
    BoolExpr* node = stack.back();  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    stack.pop_back();  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (node == nullptr) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      continue;  // LCOV_EXCL_LINE
    }
    if (node->getOp() == Op::AND) {  // LCOV_EXCL_LINE
      stack.push_back(node->getLeft());  // LCOV_EXCL_LINE
      stack.push_back(node->getRight());  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (const auto pair = simpleVariableEqualityPair(node);  // LCOV_EXCL_LINE
        pair.has_value() && seen.insert(*pair).second) {  // LCOV_EXCL_LINE
      equalities.emplace_back(pair->first, pair->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return equalities;  // LCOV_EXCL_LINE
}

// LCOV_EXCL_START
class ResetConstantEvaluator {
// LCOV_EXCL_STOP
 public:
  ResetConstantEvaluator(const KInductionProblem& problem,
                         const TransitionExprResolver& transitionByState)
      : problem_(problem),
        transitionByState_(transitionByState),
        exprMemoByStep_(problem.resetBootstrapCycles + 1) {
    resetInputs_.reserve(problem.resetBootstrapInputs.size());
    for (const auto& [symbol, value] : problem.resetBootstrapInputs) {
      resetInputs_.emplace(symbol, value);
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    initialStates_.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      initialStates_.emplace(symbol, value);  // LCOV_EXCL_LINE
    }
    bootstrapStates_.reserve(problem.bootstrapStateAssignments.size());
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      bootstrapStates_.emplace(symbol, value);
    }
  }

  // LCOV_EXCL_START
  std::optional<bool> stateValue(size_t symbol, size_t step) {
  // LCOV_EXCL_STOP
    if (budgetExhausted_) {
      return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    if (step == problem_.resetBootstrapCycles) {
    // LCOV_EXCL_STOP
      if (const auto it = bootstrapStates_.find(symbol);
          it != bootstrapStates_.end()) {
        return it->second;
      }
    // LCOV_EXCL_START
    }

    const SymbolPair key{symbol, step};
    if (const auto it = stateMemo_.find(key); it != stateMemo_.end()) {
    // LCOV_EXCL_STOP
      return it->second;  // LCOV_EXCL_LINE
    }
    if (++stateEvaluations_ > kMaxResetConstantEvaluatorStates) {
      budgetExhausted_ = true;  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    std::optional<bool> value;
    if (step == 0) {
      if (const auto it = initialStates_.find(symbol);  // LCOV_EXCL_LINE
          it != initialStates_.end()) {  // LCOV_EXCL_LINE
        value = it->second;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    } else if (transitionByState_.contains(symbol)) {
      // A state bit at reset step N is obtained by evaluating its transition
      // expression in reset step N-1. This recursively follows only the cube's
      // LCOV_EXCL_START
      // required reset cone and short-circuits through reset mux constants.
      // LCOV_EXCL_STOP
      value = exprValue(transitionByState_.at(symbol), step - 1);
    }

    stateMemo_.emplace(key, value);
    // LCOV_EXCL_START
    return value;
    // LCOV_EXCL_STOP
  }

  // LCOV_EXCL_START
  bool budgetExhausted() const { return budgetExhausted_; }


// LCOV_EXCL_STOP
 private:
  std::optional<bool> exprValue(BoolExpr* expr, size_t step) {
    if (budgetExhausted_ || expr == nullptr || step >= exprMemoByStep_.size()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    // LCOV_EXCL_START
    auto& memo = exprMemoByStep_[step];
    // LCOV_EXCL_STOP
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;  // LCOV_EXCL_LINE
    }
    if (++exprEvaluations_ > kMaxResetConstantEvaluatorExprs) {
      // LCOV_EXCL_START
      budgetExhausted_ = true;  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }


// LCOV_EXCL_STOP
    std::optional<bool> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          value = expr->getId() == 1;  // LCOV_EXCL_LINE
        } else if (const auto resetIt = resetInputs_.find(expr->getId());
                   resetIt != resetInputs_.end()) {
          value = resetIt->second;
        } else {
          const auto& stateSymbols = transitionByState_.stateSymbols();  // LCOV_EXCL_LINE
          if (stateSymbols.find(expr->getId()) != stateSymbols.end()) {  // LCOV_EXCL_LINE
            value = stateValue(expr->getId(), step);  // LCOV_EXCL_LINE
          }  // LCOV_EXCL_LINE
        }
        // LCOV_EXCL_START
        break;
      case Op::NOT:
        if (const auto operand = exprValue(expr->getLeft(), step);
            operand.has_value()) {
          value = !*operand;
        }
        break;
        // LCOV_EXCL_STOP
      case Op::AND: {
        const auto lhs = exprValue(expr->getLeft(), step);
        // LCOV_EXCL_START
        if (lhs.has_value() && !*lhs) {
          value = false;
          break;
        }
        // LCOV_EXCL_STOP
        const auto rhs = exprValue(expr->getRight(), step);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        if (rhs.has_value() && !*rhs) {
          value = false;
        } else if (lhs.has_value() && rhs.has_value()) {
          value = *lhs && *rhs;  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        break;
      }
      // LCOV_EXCL_STOP
      case Op::OR: {
        const auto lhs = exprValue(expr->getLeft(), step);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        if (lhs.has_value() && *lhs) {  // LCOV_EXCL_LINE
          value = true;  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        const auto rhs = exprValue(expr->getRight(), step);  // LCOV_EXCL_LINE
        if (rhs.has_value() && *rhs) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          value = true;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        } else if (lhs.has_value() && rhs.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          value = *lhs || *rhs;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        break;  // LCOV_EXCL_LINE
      }
      case Op::XOR: {
        const auto lhs = exprValue(expr->getLeft(), step);  // LCOV_EXCL_LINE
        const auto rhs = exprValue(expr->getRight(), step);  // LCOV_EXCL_LINE
        if (lhs.has_value() && rhs.has_value()) {  // LCOV_EXCL_LINE
          value = *lhs != *rhs;  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        break;  // LCOV_EXCL_LINE
    }

    memo.emplace(expr, value);
    return value;
  }

  const KInductionProblem& problem_;
  const TransitionExprResolver& transitionByState_;
  std::unordered_map<size_t, bool> resetInputs_;
  std::unordered_map<size_t, bool> initialStates_;
  // LCOV_EXCL_START
  std::unordered_map<size_t, bool> bootstrapStates_;
  // LCOV_EXCL_STOP
  std::unordered_map<SymbolPair, std::optional<bool>, SymbolPairHash> stateMemo_;
  std::vector<std::unordered_map<BoolExpr*, std::optional<bool>>> exprMemoByStep_;
  size_t stateEvaluations_ = 0;
  size_t exprEvaluations_ = 0;
  bool budgetExhausted_ = false;
};

std::optional<StateCube> resetSpecializedConstantConflictCube(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    const StateCube& cube) {
    // LCOV_EXCL_STOP
  if (problem.resetBootstrapCycles == 0) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  ResetConstantEvaluator evaluator(problem, transitionByState);
  for (const auto& literal : cube) {
    const auto resetValue =
        evaluator.stateValue(literal.symbol, problem.resetBootstrapCycles);
    if (resetValue.has_value() && *resetValue != literal.value) {
      return StateCube{literal};
    }
    if (evaluator.budgetExhausted()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }
  return std::nullopt;
}

bool cubeContradictsResetSpecializedConstants(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube) {
  return resetSpecializedConstantConflictCube(
      problem, transitionByState, cube).has_value();
}

// LCOV_EXCL_START
class ResetSymbolicEvaluator {
// LCOV_EXCL_STOP
 public:
  ResetSymbolicEvaluator(const KInductionProblem& problem,
                         const TransitionExprResolver& transitionByState)
      : problem_(problem),
        transitionByState_(transitionByState),
        exprMemoByStep_(problem.resetBootstrapCycles + 1) {
    resetInputs_.reserve(problem.resetBootstrapInputs.size());
    for (const auto& [symbol, value] : problem.resetBootstrapInputs) {
      resetInputs_.emplace(symbol, value);
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    initialStates_.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      initialStates_.emplace(symbol, value);  // LCOV_EXCL_LINE
    }
    bootstrapStates_.reserve(problem.bootstrapStateAssignments.size());
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      bootstrapStates_.emplace(symbol, value);
    }
  }

  std::optional<BoolExpr*> stateExpr(size_t symbol, size_t step) {
    if (budgetExhausted_) {
      return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    if (step == problem_.resetBootstrapCycles) {
    // LCOV_EXCL_STOP
      if (const auto it = bootstrapStates_.find(symbol);
          it != bootstrapStates_.end()) {
        return it->second ? BoolExpr::createTrue() : BoolExpr::createFalse();
      }
    }

    // LCOV_EXCL_START
    const SymbolPair key{symbol, step};
    if (const auto it = stateMemo_.find(key); it != stateMemo_.end()) {
    // LCOV_EXCL_STOP
      return it->second;
    }
    if (++stateEvaluations_ > stateEvaluationLimit_) {
      budgetExhausted_ = true;  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP

    BoolExpr* result = nullptr;
    if (step == 0) {
      if (const auto it = initialStates_.find(symbol);
          it != initialStates_.end()) {
        result = it->second ? BoolExpr::createTrue() : BoolExpr::createFalse();  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      } else {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        result = BoolExpr::Var(symbol);
      }
    } else if (transitionByState_.contains(symbol)) {
      const auto value = exprValue(transitionByState_.at(symbol), step - 1);
      if (!value.has_value()) {
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      result = *value;
    } else {
      // Missing transition information is treated as an unconstrained symbolic
      // variable.  That is conservative: it can miss a reset relation shortcut,
      // but it cannot invent one.
      result = BoolExpr::Var(symbol);  // LCOV_EXCL_LINE
    }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
    stateMemo_.emplace(key, result);
    // LCOV_EXCL_START
    return result;
    // LCOV_EXCL_STOP
  }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  bool budgetExhausted() const { return budgetExhausted_; }

// LCOV_EXCL_START

  void resetBudget() {
    stateEvaluations_ = 0;
    // LCOV_EXCL_STOP
    exprEvaluations_ = 0;
    budgetExhausted_ = false;
    for (auto& active : exprActiveByStep_) {
      active.clear();
    }
  }

  size_t stateEvaluationLimit() const { return stateEvaluationLimit_; }  // LCOV_EXCL_LINE

  size_t exprEvaluationLimit() const { return exprEvaluationLimit_; }  // LCOV_EXCL_LINE

  void setBudgetLimits(size_t stateEvaluationLimit,  // LCOV_EXCL_LINE
                       size_t exprEvaluationLimit) {
    stateEvaluationLimit_ = stateEvaluationLimit;  // LCOV_EXCL_LINE
    exprEvaluationLimit_ = exprEvaluationLimit;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  const std::set<size_t>* cachedSupportVars(BoolExpr* expr);

 private:
  static bool isBoolConst(BoolExpr* expr, bool value) {
    return expr == (value ? BoolExpr::createTrue() : BoolExpr::createFalse());
  }

  void ensureStepCaches(size_t step) {
    if (step >= exprMemoByStep_.size()) {
      exprMemoByStep_.resize(step + 1);  // LCOV_EXCL_LINE
    }
    if (step >= cheapExprMemoByStep_.size()) {
      cheapExprMemoByStep_.resize(step + 1);  // LCOV_EXCL_LINE
    }
    if (step >= exprMissesByStep_.size()) {
      exprMissesByStep_.resize(step + 1);  // LCOV_EXCL_LINE
    }
    if (step >= cheapExprMissesByStep_.size()) {
      cheapExprMissesByStep_.resize(step + 1);  // LCOV_EXCL_LINE
    }
    if (step >= exprActiveByStep_.size()) {
      exprActiveByStep_.resize(step + 1);  // LCOV_EXCL_LINE
    }
  }

  std::optional<BoolExpr*> cheapExprValue(
      BoolExpr* expr,
      size_t step,
      size_t& remainingBudget) {
    if (expr == nullptr || remainingBudget == 0) {
      return std::nullopt;
    }
    ensureStepCaches(step);
    auto& memo = cheapExprMemoByStep_[step];
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;
    }
    auto& misses = cheapExprMissesByStep_[step];
    if (misses.find(expr) != misses.end()) {
      return std::nullopt;
    }
    --remainingBudget;

    std::optional<BoolExpr*> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          value = expr;
          break;
        // LCOV_EXCL_START
        }
        if (const auto resetIt = resetInputs_.find(expr->getId());
        // LCOV_EXCL_STOP
            resetIt != resetInputs_.end()) {
          const bool resetValue =
              step < problem_.resetBootstrapCycles
                  ? resetIt->second
                  : !resetIt->second;
          // LCOV_EXCL_START
          value = resetValue ? BoolExpr::createTrue()
                             : BoolExpr::createFalse();
          break;
                            // LCOV_EXCL_STOP
        }
        if (step == 0) {
          if (const auto it = initialStates_.find(expr->getId());
              it != initialStates_.end()) {
            value = it->second ? BoolExpr::createTrue()  // LCOV_EXCL_LINE
                               : BoolExpr::createFalse();  // LCOV_EXCL_LINE
            break;  // LCOV_EXCL_LINE
          }
        }
        if (step == problem_.resetBootstrapCycles) {
          if (const auto it = bootstrapStates_.find(expr->getId());
              it != bootstrapStates_.end()) {
            value = it->second ? BoolExpr::createTrue()  // LCOV_EXCL_LINE
                               : BoolExpr::createFalse();  // LCOV_EXCL_LINE
            break;  // LCOV_EXCL_LINE
          }
        }
        if (step > 0 && transitionByState_.contains(expr->getId())) {
          value = cheapExprValue(
              transitionByState_.at(expr->getId()), step - 1, remainingBudget);
          break;
        }
        break;
      case Op::NOT:
        if (const auto operand =
                cheapExprValue(expr->getLeft(), step, remainingBudget);
            operand.has_value()) {
          // LCOV_EXCL_START
          value = BoolExpr::Not(*operand);
          // LCOV_EXCL_STOP
        }
        break;
      case Op::AND: {
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          // LCOV_EXCL_START
          value = BoolExpr::createFalse();
          // LCOV_EXCL_STOP
          break;
        }
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
          value = BoolExpr::createFalse();
          break;
        }
        if (lhs.has_value() && rhs.has_value()) {
          // LCOV_EXCL_START
          value = BoolExpr::And(*lhs, *rhs);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          break;  // LCOV_EXCL_LINE
        }
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          value = rhs;  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          value = lhs;  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        break;
      }
      // LCOV_EXCL_START
      case Op::OR: {
      // LCOV_EXCL_STOP
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          // LCOV_EXCL_START
          value = BoolExpr::createTrue();  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          break;  // LCOV_EXCL_LINE
        }
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          value = BoolExpr::createTrue();  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        if (lhs.has_value() && rhs.has_value()) {
          value = BoolExpr::Or(*lhs, *rhs);  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          value = rhs;  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        // LCOV_EXCL_START
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
        // LCOV_EXCL_STOP
          value = lhs;  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        break;
      }
      case Op::XOR: {
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        // LCOV_EXCL_START
        if (lhs.has_value() && rhs.has_value()) {
        // LCOV_EXCL_STOP
          value = BoolExpr::Xor(*lhs, *rhs);  // LCOV_EXCL_LINE
        } // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        break;
      }
      // LCOV_EXCL_STOP
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        break;  // LCOV_EXCL_LINE
    }
    if (value.has_value()) {
      memo.emplace(expr, *value);
    } else if (remainingBudget != 0) {
      // Cache structural misses too. Swerv final leaves repeatedly revisit the
      // same reset DAG nodes while validating neighboring root cubes.
      misses.emplace(expr);
    }
    return value;
  }

  std::optional<BoolExpr*> cheapChildExprValue(BoolExpr* expr,
                                               size_t step) {
    size_t cheapEvalBudget = kMaxResetSymbolicCheapEvalNodes;
    return cheapExprValue(expr, step, cheapEvalBudget);
  }

  // LCOV_EXCL_START
  std::optional<BoolExpr*> exprValue(BoolExpr* expr, size_t step) {
    if (budgetExhausted_ || expr == nullptr) {
    // LCOV_EXCL_STOP
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    ensureStepCaches(step);  // LCOV_EXCL_LINE

    auto& memo = exprMemoByStep_[step];
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;
    }
    auto& misses = exprMissesByStep_[step];
    if (misses.find(expr) != misses.end()) {
      return std::nullopt; // LCOV_EXCL_LINE
    }
    auto& active = exprActiveByStep_[step];
    if (!active.insert(expr).second) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    struct ActiveGuard {
      std::unordered_set<BoolExpr*>& active;
      BoolExpr* expr = nullptr;
      ~ActiveGuard() { active.erase(expr); }
    } activeGuard{active, expr};
    if (++exprEvaluations_ > exprEvaluationLimit_) {
      budgetExhausted_ = true;  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
    size_t cheapEvalBudget = kMaxResetSymbolicCheapEvalNodes;
    if (const auto cheapValue =
            cheapExprValue(expr, step, cheapEvalBudget);
        cheapValue.has_value()) {
      memo.emplace(expr, *cheapValue);
      // LCOV_EXCL_START
      return *cheapValue;
    }

    std::optional<BoolExpr*> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
        // LCOV_EXCL_STOP
          value = expr;  // LCOV_EXCL_LINE
        } else if (const auto resetIt = resetInputs_.find(expr->getId());
                   resetIt != resetInputs_.end()) {
          // Reset controls are asserted during bootstrap frames and deasserted
          // LCOV_EXCL_START
          // afterward.  This lets the reset-specialized proof reason about
          // LCOV_EXCL_STOP
          // post-reset candidate cubes without opening the full SAT unroll.
          const bool resetValue =  // LCOV_EXCL_LINE
              step < problem_.resetBootstrapCycles  // LCOV_EXCL_LINE
                  ? resetIt->second  // LCOV_EXCL_LINE
                  : !resetIt->second;  // LCOV_EXCL_LINE
          value = resetValue ? BoolExpr::createTrue()  // LCOV_EXCL_LINE
                             : BoolExpr::createFalse();  // LCOV_EXCL_LINE
        } else {  // LCOV_EXCL_LINE
          const auto& stateSymbols = transitionByState_.stateSymbols();
          if (stateSymbols.find(expr->getId()) != stateSymbols.end()) {
            value = stateExpr(expr->getId(), step);
          } else {
            // LCOV_EXCL_START
            value = expr;  // LCOV_EXCL_LINE
          }
          // LCOV_EXCL_STOP
        }
        break;
      case Op::NOT:
        // LCOV_EXCL_START
        if (const auto operand = exprValue(expr->getLeft(), step);
            operand.has_value()) {
            // LCOV_EXCL_STOP
          value = BoolExpr::Not(*operand);
        }
        break;
      case Op::AND: {
        const auto lhsCheap = cheapChildExprValue(expr->getLeft(), step);
        if (lhsCheap.has_value() && isBoolConst(*lhsCheap, false)) {
          value = BoolExpr::createFalse(); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        const auto rhsCheap = cheapChildExprValue(expr->getRight(), step);
        if (rhsCheap.has_value() && isBoolConst(*rhsCheap, false)) {
          value = BoolExpr::createFalse(); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        if (lhsCheap.has_value() && isBoolConst(*lhsCheap, true)) {
          value = exprValue(expr->getRight(), step); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        if (rhsCheap.has_value() && isBoolConst(*rhsCheap, true)) {
          value = exprValue(expr->getLeft(), step);
          break;
        }
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          value = BoolExpr::createFalse();  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        // LCOV_EXCL_START
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
        // LCOV_EXCL_STOP
          value = BoolExpr::createFalse();  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        // LCOV_EXCL_START
        if (lhs.has_value() && rhs.has_value()) {
          value = BoolExpr::And(*lhs, *rhs);
          // LCOV_EXCL_STOP
        }
        break;
      }
      case Op::OR: {
        const auto lhsCheap = cheapChildExprValue(expr->getLeft(), step);
        if (lhsCheap.has_value() && isBoolConst(*lhsCheap, true)) {
          value = BoolExpr::createTrue(); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        const auto rhsCheap = cheapChildExprValue(expr->getRight(), step);
        if (rhsCheap.has_value() && isBoolConst(*rhsCheap, true)) {
          value = BoolExpr::createTrue(); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        if (lhsCheap.has_value() && isBoolConst(*lhsCheap, false)) {
          value = exprValue(expr->getRight(), step); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        if (rhsCheap.has_value() && isBoolConst(*rhsCheap, false)) {
          value = exprValue(expr->getLeft(), step); // LCOV_EXCL_LINE
          break; // LCOV_EXCL_LINE
        }
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          value = BoolExpr::createTrue();  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          value = BoolExpr::createTrue();  // LCOV_EXCL_LINE
          break;  // LCOV_EXCL_LINE
        }
        // LCOV_EXCL_START
        if (lhs.has_value() && rhs.has_value()) {
        // LCOV_EXCL_STOP
          value = BoolExpr::Or(*lhs, *rhs);
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        break;
      }
      case Op::XOR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        const auto rhs = exprValue(expr->getRight(), step);
        if (lhs.has_value() && rhs.has_value()) {
          value = BoolExpr::Xor(*lhs, *rhs);
        }
        break;
      }
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        break;  // LCOV_EXCL_LINE
    }

    if (value.has_value()) {
      memo.emplace(expr, *value);
    } else if (!budgetExhausted_) {
      // A non-budget miss is deterministic for this problem/step; memoizing it
      // avoids re-walking unresolved transition cones during root validation.
      misses.emplace(expr); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    return value;
  }

  const KInductionProblem& problem_;
  const TransitionExprResolver& transitionByState_;
  std::unordered_map<size_t, bool> resetInputs_;
  std::unordered_map<size_t, bool> initialStates_;
  std::unordered_map<size_t, bool> bootstrapStates_;
  // LCOV_EXCL_START
  std::unordered_map<SymbolPair, BoolExpr*, SymbolPairHash> stateMemo_;
  // LCOV_EXCL_STOP
  std::vector<std::unordered_map<BoolExpr*, BoolExpr*>> exprMemoByStep_;
  std::vector<std::unordered_map<BoolExpr*, BoolExpr*>> cheapExprMemoByStep_;
  std::vector<std::unordered_set<BoolExpr*>> exprMissesByStep_;
  std::vector<std::unordered_set<BoolExpr*>> cheapExprMissesByStep_;
  std::vector<std::unordered_set<BoolExpr*>> exprActiveByStep_;
  std::unordered_map<BoolExpr*, std::set<size_t>> supportMemo_;
  // LCOV_EXCL_START
  std::unordered_set<BoolExpr*> supportMisses_;
  size_t stateEvaluationLimit_ = kMaxResetSymbolicEvaluatorStates;
  size_t exprEvaluationLimit_ = kMaxResetSymbolicEvaluatorExprs;
  size_t stateEvaluations_ = 0;
  size_t exprEvaluations_ = 0;
  bool budgetExhausted_ = false;
  // LCOV_EXCL_STOP
};

class ScopedResetSymbolicEvaluatorBudget {
 public:
  ScopedResetSymbolicEvaluatorBudget(ResetSymbolicEvaluator& evaluator,  // LCOV_EXCL_LINE
                                     size_t stateEvaluationLimit,
                                     // LCOV_EXCL_START
                                     size_t exprEvaluationLimit)
      : evaluator_(evaluator),  // LCOV_EXCL_LINE
        previousStateEvaluationLimit_(evaluator.stateEvaluationLimit()),  // LCOV_EXCL_LINE
        previousExprEvaluationLimit_(evaluator.exprEvaluationLimit()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
    evaluator_.setBudgetLimits(stateEvaluationLimit, exprEvaluationLimit);  // LCOV_EXCL_LINE
    evaluator_.resetBudget();  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  ScopedResetSymbolicEvaluatorBudget(
      const ScopedResetSymbolicEvaluatorBudget&) = delete;
  ScopedResetSymbolicEvaluatorBudget& operator=(
      const ScopedResetSymbolicEvaluatorBudget&) = delete;

  ~ScopedResetSymbolicEvaluatorBudget() {  // LCOV_EXCL_LINE
    evaluator_.setBudgetLimits(  // LCOV_EXCL_LINE
        previousStateEvaluationLimit_, previousExprEvaluationLimit_);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

 private:
  ResetSymbolicEvaluator& evaluator_;
  size_t previousStateEvaluationLimit_ = 0;
  size_t previousExprEvaluationLimit_ = 0;
};

ResetSymbolicEvaluator& resetSymbolicEvaluatorFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState) {
  if (cache.resetExpressionEvaluator == nullptr ||
      cache.resetExpressionProblem != &problem ||
      cache.resetExpressionTransitions != &transitionByState) {
    cache.resetExpressionEvaluator =
        std::make_shared<ResetSymbolicEvaluator>(problem, transitionByState);
    cache.resetExpressionProblem = &problem;
    cache.resetExpressionTransitions = &transitionByState;
  } else {
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag("SEC PDR stats: reset-specialized expression cache reuse");
    }
    cache.resetExpressionEvaluator->resetBudget();
  }
  return *cache.resetExpressionEvaluator;
}

// LCOV_EXCL_START
bool isConstExpr(BoolExpr* expr, bool value) {
// LCOV_EXCL_STOP
  return expr == (value ? BoolExpr::createTrue() : BoolExpr::createFalse());
}

bool areComplementExprs(BoolExpr* lhs, BoolExpr* rhs) {
  return BoolExpr::Not(lhs) == rhs || BoolExpr::Not(rhs) == lhs;
}

std::optional<bool> constExprValue(BoolExpr* expr) {
  // LCOV_EXCL_START
  if (expr == BoolExpr::createFalse()) {
  // LCOV_EXCL_STOP
    return false;
  }
  if (expr == BoolExpr::createTrue()) {
    return true;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return std::nullopt;
}

// LCOV_EXCL_START

class BoolExprEqualityIndex {
// LCOV_EXCL_STOP
 public:
  void unite(BoolExpr* lhs, BoolExpr* rhs) {
    if (lhs == nullptr || rhs == nullptr) {
      return;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    BoolExpr* lhsRoot = find(lhs);
    // LCOV_EXCL_STOP
    BoolExpr* rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      return;  // LCOV_EXCL_LINE
    }
    if (rhsRoot < lhsRoot) {
      std::swap(lhsRoot, rhsRoot);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    parent_[rhsRoot] = lhsRoot;
  }

  bool equivalent(BoolExpr* lhs, BoolExpr* rhs) {
    if (lhs == nullptr || rhs == nullptr) {
      return false;  // LCOV_EXCL_LINE
    }
    return find(lhs) == find(rhs);
  }

 private:
  BoolExpr* find(BoolExpr* expr) {
    const auto [it, inserted] = parent_.emplace(expr, expr);
    if (inserted || it->second == expr) {
      return expr;
    }
    it->second = find(it->second);
    return it->second;
  }

  // LCOV_EXCL_START
  std::unordered_map<BoolExpr*, BoolExpr*> parent_;
  // LCOV_EXCL_STOP
};

class BoolExprEqualityRewriter {
 public:
  void refineToFixedPoint(
      const std::vector<std::pair<BoolExpr*, BoolExpr*>>& equalities) {
    for (size_t pass = 0; pass <= equalities.size(); ++pass) {
      bool changed = false;
      memo_.clear();
      for (const auto& [lhs, rhs] : equalities) {
        // LCOV_EXCL_START
        changed |= unite(rewrite(lhs), rewrite(rhs));
        // LCOV_EXCL_STOP
        if (inconsistent_) {
          return;  // LCOV_EXCL_LINE
        }
      }
      if (!changed) {
        return;
      }
    }
  }

  BoolExpr* rewrite(BoolExpr* expr) {
    if (expr == nullptr) {
      return nullptr;  // LCOV_EXCL_LINE
    }
    if (const auto it = memo_.find(expr); it != memo_.end()) {
      return find(it->second);
    }

    BoolExpr* rewritten = expr;
    switch (expr->getOp()) {
      case Op::VAR:
        rewritten = expr;
        // LCOV_EXCL_START
        break;
      case Op::NOT:
        rewritten = BoolExpr::Not(rewrite(expr->getLeft()));
        break;
        // LCOV_EXCL_STOP
      case Op::AND:
        // LCOV_EXCL_START
        rewritten = BoolExpr::And(
        // LCOV_EXCL_STOP
            rewrite(expr->getLeft()), rewrite(expr->getRight()));
        break;
      case Op::OR:
        rewritten = BoolExpr::Or( // LCOV_EXCL_LINE
            rewrite(expr->getLeft()), rewrite(expr->getRight())); // LCOV_EXCL_LINE
        break; // LCOV_EXCL_LINE
      case Op::XOR:
        rewritten = BoolExpr::Xor(  // LCOV_EXCL_LINE
            rewrite(expr->getLeft()), rewrite(expr->getRight()));  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        // LCOV_EXCL_START
        break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
    }

    rewritten = find(rewritten);
    memo_.emplace(expr, rewritten);
    return rewritten;
  }

  // LCOV_EXCL_START
  bool inconsistent() const { return inconsistent_; }

 private:
  bool unite(BoolExpr* lhs, BoolExpr* rhs) {
  // LCOV_EXCL_STOP
    if (lhs == nullptr || rhs == nullptr) {
      // LCOV_EXCL_START
      return false;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    BoolExpr* lhsRoot = find(lhs);
    BoolExpr* rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      return false;
    }
    if (const auto lhsConst = constExprValue(lhsRoot)) {
      if (const auto rhsConst = constExprValue(rhsRoot);  // LCOV_EXCL_LINE
          rhsConst.has_value() && *lhsConst != *rhsConst) {  // LCOV_EXCL_LINE
        inconsistent_ = true;  // LCOV_EXCL_LINE
        return false;  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE

    BoolExpr* root = preferredRoot(lhsRoot, rhsRoot);
    BoolExpr* child = root == lhsRoot ? rhsRoot : lhsRoot;
    parent_[child] = root;
    memo_.clear();
    return true;
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP

  BoolExpr* find(BoolExpr* expr) {
    // LCOV_EXCL_START
    const auto [it, inserted] = parent_.emplace(expr, expr);
    // LCOV_EXCL_STOP
    if (inserted || it->second == expr) {
      return expr;
    }
    it->second = find(it->second);
    return it->second;
  }

  static BoolExpr* preferredRoot(BoolExpr* lhs, BoolExpr* rhs) {
    if (constExprValue(lhs).has_value()) {
      return lhs;  // LCOV_EXCL_LINE
    }
    if (constExprValue(rhs).has_value()) {
      return rhs;  // LCOV_EXCL_LINE
    }
    return rhs < lhs ? rhs : lhs;
  }

  std::unordered_map<BoolExpr*, BoolExpr*> parent_;
  std::unordered_map<BoolExpr*, BoolExpr*> memo_;
  // LCOV_EXCL_START
  bool inconsistent_ = false;
  // LCOV_EXCL_STOP
};

struct ResetBootstrapExpressionRelations {
  BoolExprEqualityIndex index;
  BoolExprEqualityRewriter rewriter;
  bool hasRelation = false;
  bool hasRewriter = false;
};

bool bootstrapExpressionRewriteBudgetAllows(
    const std::vector<std::pair<BoolExpr*, BoolExpr*>>& equalities) {
  if (equalities.size() > kMaxBootstrapExpressionRewritePairs) {
    return false;  // LCOV_EXCL_LINE
  }

  std::unordered_set<BoolExpr*> visited;
  std::vector<BoolExpr*> stack;
  visited.reserve(kMaxBootstrapExpressionRewriteNodes);
  // LCOV_EXCL_START
  stack.reserve(equalities.size() * 2);
  // LCOV_EXCL_STOP
  for (const auto& [lhs, rhs] : equalities) {
    if (lhs != nullptr) {
      // LCOV_EXCL_START
      stack.push_back(lhs);
      // LCOV_EXCL_STOP
    }
    if (rhs != nullptr) {
      // LCOV_EXCL_START
      stack.push_back(rhs);
    }
    // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    // LCOV_EXCL_STOP
    stack.pop_back();
    if (!visited.insert(node).second) {
      continue;  // LCOV_EXCL_LINE
    }
    if (visited.size() > kMaxBootstrapExpressionRewriteNodes) {
      return false;  // LCOV_EXCL_LINE
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return true;
}

std::optional<StateCube> findResetExpressionRelationConflict(
    const std::vector<BoolExpr*>& expressions,
    const StateCube& cube,
    // LCOV_EXCL_START
    BoolExprEqualityIndex* equalityIndex = nullptr) {
  for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
      const bool equivalent =
          equalityIndex != nullptr
          // LCOV_EXCL_STOP
              ? equalityIndex->equivalent(expressions[lhs], expressions[rhs])
              : expressions[lhs] == expressions[rhs];
      if (equivalent && cube[lhs].value != cube[rhs].value) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
      if (areComplementExprs(expressions[lhs], expressions[rhs]) &&
          cube[lhs].value == cube[rhs].value) {  // LCOV_EXCL_LINE
        StateCube conflict{cube[lhs], cube[rhs]};  // LCOV_EXCL_LINE
        normalizeCube(conflict);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return conflict;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
    }
  }
  return std::nullopt;
}

// LCOV_EXCL_START
bool structuralImplies(
// LCOV_EXCL_STOP
    BoolExpr* lhs,
    BoolExpr* rhs,
    std::unordered_map<ExprPair, bool, ExprPairHash>& memo,
    size_t& budget) {
  if (lhs == nullptr || rhs == nullptr || budget == 0) {
    return false;  // LCOV_EXCL_LINE
  }
  --budget;
  if (lhs == rhs) {
    return true;
  }
  if (const auto lhsConst = constExprValue(lhs)) {
    return !*lhsConst || rhs == BoolExpr::createTrue();  // LCOV_EXCL_LINE
  }
  if (const auto rhsConst = constExprValue(rhs)) {
    return *rhsConst;
  }

  const ExprPair key{lhs, rhs};
  if (const auto it = memo.find(key); it != memo.end()) {
    return it->second;
  }
  // Insert a conservative value before recursing. BoolExprs are DAGs, but a
  // defensive visited value keeps future rewrites from creating implication
  // LCOV_EXCL_START
  // recursion if more Boolean identities are added.
  memo.emplace(key, false);
  // LCOV_EXCL_STOP

  bool result = false;
  if (lhs->getOp() == Op::AND) {
    // (a & b) => a, and transitively to anything either child implies.
    // LCOV_EXCL_START
    result = structuralImplies(lhs->getLeft(), rhs, memo, budget) ||
    // LCOV_EXCL_STOP
             structuralImplies(lhs->getRight(), rhs, memo, budget);
  } else if (lhs->getOp() == Op::OR) {
    // (a | b) => c only when both alternatives imply c.
    result = structuralImplies(lhs->getLeft(), rhs, memo, budget) &&
             structuralImplies(lhs->getRight(), rhs, memo, budget);
  } else if (lhs->getOp() == Op::NOT && rhs->getOp() == Op::NOT) {
    result = structuralImplies(rhs->getLeft(), lhs->getLeft(), memo, budget);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  if (!result && rhs->getOp() == Op::AND) {
    // a => (b & c) only when a implies both conjuncts.
    result = structuralImplies(lhs, rhs->getLeft(), memo, budget) &&
             structuralImplies(lhs, rhs->getRight(), memo, budget);  // LCOV_EXCL_LINE
  } else if (!result && rhs->getOp() == Op::OR) {
    // a => (b | c) if a implies either disjunct.
    result = structuralImplies(lhs, rhs->getLeft(), memo, budget) ||
             structuralImplies(lhs, rhs->getRight(), memo, budget);
  }

  memo[key] = result;
  return result;
}

std::optional<StateCube> findResetExpressionImplicationConflict(
    // LCOV_EXCL_START
    const std::vector<BoolExpr*>& expressions,
    const StateCube& cube) {
  // Keep this shortcut cheap on large industrial cubes. It is a conservative
  // proof search: exhausting the shared budget only disables this shortcut for
  // LCOV_EXCL_STOP
  // the current cube, leaving the exact reset-frontier checks available later.
  std::unordered_map<ExprPair, bool, ExprPairHash> implicationMemo;
  size_t implicationBudget = 4096;
  for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
      if (cube[lhs].value && !cube[rhs].value &&
          structuralImplies(
              expressions[lhs], expressions[rhs],
              implicationMemo, implicationBudget)) {
        StateCube conflict{cube[lhs], cube[rhs]};  // LCOV_EXCL_LINE
        normalizeCube(conflict);  // LCOV_EXCL_LINE
        return conflict;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      if (cube[rhs].value && !cube[lhs].value &&
          structuralImplies(
              expressions[rhs], expressions[lhs],
              implicationMemo, implicationBudget)) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
    // LCOV_EXCL_START
    }
  }
  return std::nullopt;
}

class ResetExpressionCanonicalizer {
// LCOV_EXCL_STOP
 public:
  explicit ResetExpressionCanonicalizer(const KInductionProblem& problem) {
    parent_.reserve(
        (problem.initialStateEqualityPairs.size() +
         problem.sameFrameStateEqualityPairs0.size() +
         problem.sameFrameStateEqualityPairs1.size()) *
        2);
    if (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
      for (const auto& [lhsSymbol, rhsSymbol] :
           problem.initialStateEqualityPairs) {
        unite(lhsSymbol, rhsSymbol);
      }
    }
    for (const auto& [lhsSymbol, rhsSymbol] :
         problem.sameFrameStateEqualityPairs0) {
      unite(lhsSymbol, rhsSymbol); // LCOV_EXCL_LINE
    }
    for (const auto& [lhsSymbol, rhsSymbol] :
         problem.sameFrameStateEqualityPairs1) {
      unite(lhsSymbol, rhsSymbol); // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
    // LCOV_EXCL_STOP
      const size_t root = find(symbol);  // LCOV_EXCL_LINE
      if (const auto it = rootAssignments_.find(root);  // LCOV_EXCL_LINE
          it != rootAssignments_.end() && it->second != value) {  // LCOV_EXCL_LINE
        inconsistent_ = true;  // LCOV_EXCL_LINE
      } else {  // LCOV_EXCL_LINE
        rootAssignments_[root] = value;  // LCOV_EXCL_LINE
      }
    }
  }

  BoolExpr* canonicalize(BoolExpr* expr) {
    if (expr == nullptr) {
      return nullptr;  // LCOV_EXCL_LINE
    }
    if (const auto it = memo_.find(expr); it != memo_.end()) {
      // LCOV_EXCL_START
      return it->second;
    }


// LCOV_EXCL_STOP
    BoolExpr* result = expr;
    switch (expr->getOp()) {
      case Op::VAR: {
        const size_t symbol = expr->getId();
        if (symbol < 2) {
          result = expr;
        } else {
          const size_t root = find(symbol);
          if (const auto assignment = rootAssignments_.find(root);
              assignment != rootAssignments_.end()) {
            result = assignment->second ? BoolExpr::createTrue()  // LCOV_EXCL_LINE
                                        : BoolExpr::createFalse();  // LCOV_EXCL_LINE
          } else {  // LCOV_EXCL_LINE
            result = BoolExpr::Var(root);
          }
        }
        break;
      }
      case Op::NOT:
        result = BoolExpr::Not(canonicalize(expr->getLeft()));
        // LCOV_EXCL_START
        break;
        // LCOV_EXCL_STOP
      case Op::AND:
        // LCOV_EXCL_START
        result = canonicalAnd(
        // LCOV_EXCL_STOP
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        break;
      case Op::OR:
        result = canonicalOr(
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        break;
      // LCOV_EXCL_START
      case Op::XOR:
      // LCOV_EXCL_STOP
        result = BoolExpr::Xor(
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        // LCOV_EXCL_START
        break;
      case Op::NONE:  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      default:
        // LCOV_EXCL_START
        break;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP

    // LCOV_EXCL_START
    memo_.emplace(expr, result);
    return result;
    // LCOV_EXCL_STOP
  }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  std::optional<BoolExpr*> canonicalizeBounded(  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      BoolExpr* expr,
      size_t& remainingNodes) {
      // LCOV_EXCL_STOP
    if (expr == nullptr) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return nullptr;  // LCOV_EXCL_LINE
    }
    if (const auto it = memo_.find(expr); it != memo_.end()) {  // LCOV_EXCL_LINE
      return it->second;  // LCOV_EXCL_LINE
    }
    if (remainingNodes == 0) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    --remainingNodes;  // LCOV_EXCL_LINE

    BoolExpr* result = expr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    switch (expr->getOp()) {  // LCOV_EXCL_LINE
      case Op::VAR: {
        // LCOV_EXCL_START
        const size_t symbol = expr->getId();  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        if (symbol < 2) {  // LCOV_EXCL_LINE
          result = expr;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        } else {  // LCOV_EXCL_LINE
          const size_t root = find(symbol);  // LCOV_EXCL_LINE
          if (const auto assignment = rootAssignments_.find(root);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
              assignment != rootAssignments_.end()) {  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            result = assignment->second ? BoolExpr::createTrue()  // LCOV_EXCL_LINE
                                        : BoolExpr::createFalse();  // LCOV_EXCL_LINE
                                        // LCOV_EXCL_STOP
          } else {  // LCOV_EXCL_LINE
            result = BoolExpr::Var(root);  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          }
        }
        break;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
      // LCOV_EXCL_START
      case Op::NOT: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);  // LCOV_EXCL_LINE
        if (!left.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        result = BoolExpr::Not(*left);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        break;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      case Op::AND: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);  // LCOV_EXCL_LINE
        if (!left.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);  // LCOV_EXCL_LINE
        if (!right.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        result = canonicalAnd(*left, *right);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        break;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      case Op::OR: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);  // LCOV_EXCL_LINE
        if (!left.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);  // LCOV_EXCL_LINE
        if (!right.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        result = canonicalOr(*left, *right);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        break;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      case Op::XOR: {
        // LCOV_EXCL_START
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        if (!left.has_value()) {  // LCOV_EXCL_LINE
          return std::nullopt;  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);  // LCOV_EXCL_LINE
        if (!right.has_value()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          return std::nullopt;  // LCOV_EXCL_LINE
        }
        result = BoolExpr::Xor(*left, *right);  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        break;  // LCOV_EXCL_LINE
    }

    memo_.emplace(expr, result);  // LCOV_EXCL_LINE
    return result;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  bool inconsistent() const { return inconsistent_; }

 private:
  // LCOV_EXCL_START
  size_t find(size_t symbol) {
  // LCOV_EXCL_STOP
    const auto [it, inserted] = parent_.emplace(symbol, symbol);
    if (inserted || it->second == symbol) {
      // LCOV_EXCL_START
      return symbol;
    }
    // LCOV_EXCL_STOP
    it->second = find(it->second);
    return it->second;
  }

  void unite(size_t lhsSymbol, size_t rhsSymbol) {
    size_t lhsRoot = find(lhsSymbol);
    size_t rhsRoot = find(rhsSymbol);
    if (lhsRoot == rhsRoot) {
      return;  // LCOV_EXCL_LINE
    }
    if (rhsRoot < lhsRoot) {
      std::swap(lhsRoot, rhsRoot);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    parent_[rhsRoot] = lhsRoot;
    // LCOV_EXCL_STOP
  }

  // LCOV_EXCL_START
  static bool binaryContains(BoolExpr* expr, Op op, BoolExpr* child) {
  // LCOV_EXCL_STOP
    return expr != nullptr && expr->getOp() == op &&
           (expr->getLeft() == child || expr->getRight() == child);
  }

  static BoolExpr* canonicalAnd(BoolExpr* lhs, BoolExpr* rhs) {
    // Absorption is the cheap Boolean equivalence that the sampled AES reset
    // cubes needed before falling into the expensive per-cube SAT query:
    // x & (x | y) == x.
    // LCOV_EXCL_START
    if (binaryContains(lhs, Op::OR, rhs)) {
    // LCOV_EXCL_STOP
      return rhs;  // LCOV_EXCL_LINE
    }
    if (binaryContains(rhs, Op::OR, lhs)) {
      return lhs;  // LCOV_EXCL_LINE
    }
    return BoolExpr::And(lhs, rhs);
  }

  static BoolExpr* canonicalOr(BoolExpr* lhs, BoolExpr* rhs) {
    // Dual absorption: x | (x & y) == x. This keeps structurally different
    // but Boolean-equivalent reset expressions aligned without invoking SAT.
    if (binaryContains(lhs, Op::AND, rhs)) {
      return rhs;  // LCOV_EXCL_LINE
    }
    if (binaryContains(rhs, Op::AND, lhs)) {
      return lhs;
    }
    return BoolExpr::Or(lhs, rhs);
  }

  std::unordered_map<size_t, size_t> parent_;
  std::unordered_map<size_t, bool> rootAssignments_;
  std::unordered_map<BoolExpr*, BoolExpr*> memo_;
  bool inconsistent_ = false;
};

ResetExpressionCanonicalizer& resetExpressionCanonicalizerFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem) {
  if (cache.resetExpressionCanonicalizer == nullptr ||
      cache.resetExpressionCanonicalizerProblem != &problem) {
    cache.resetExpressionCanonicalizer =
        std::make_shared<ResetExpressionCanonicalizer>(problem);
    cache.resetExpressionCanonicalizerProblem = &problem;
  }
  return *cache.resetExpressionCanonicalizer;
}

ResetBootstrapExpressionRelations* resetBootstrapExpressionRelationsFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    ResetSymbolicEvaluator& evaluator,
    ResetExpressionCanonicalizer& canonicalizer) {
  if (cache.resetBootstrapExpressionRelations != nullptr &&
      cache.resetBootstrapExpressionProblem == &problem && // LCOV_EXCL_LINE
      cache.resetBootstrapExpressionTransitions == &transitionByState) { // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return cache.resetBootstrapExpressionRelations.get();
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START
  auto relations = std::make_shared<ResetBootstrapExpressionRelations>();
  // LCOV_EXCL_STOP
  std::vector<std::pair<BoolExpr*, BoolExpr*>> bootstrapExprPairs;
  if (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
    bootstrapExprPairs.reserve(problem.bootstrapStateEqualityPairs.size());
    for (const auto& [lhsSymbol, rhsSymbol] :
         problem.bootstrapStateEqualityPairs) {
      const auto lhsExpr =
          evaluator.stateExpr(lhsSymbol, problem.resetBootstrapCycles);
      const auto rhsExpr =
          evaluator.stateExpr(rhsSymbol, problem.resetBootstrapCycles);
      if (!lhsExpr.has_value() || !rhsExpr.has_value()) {
        if (evaluator.budgetExhausted()) {  // LCOV_EXCL_LINE
          return nullptr;  // LCOV_EXCL_LINE
        }
        continue;  // LCOV_EXCL_LINE
      }
      BoolExpr* lhsCanonical = canonicalizer.canonicalize(*lhsExpr);
      BoolExpr* rhsCanonical = canonicalizer.canonicalize(*rhsExpr);
      relations->index.unite(lhsCanonical, rhsCanonical);
      bootstrapExprPairs.emplace_back(lhsCanonical, rhsCanonical);
      relations->hasRelation = true;
    }
  }

  if (relations->hasRelation &&
      bootstrapExpressionRewriteBudgetAllows(bootstrapExprPairs)) {
    relations->rewriter.refineToFixedPoint(bootstrapExprPairs);
    relations->hasRewriter = true;
  }

  cache.resetBootstrapExpressionRelations = relations;
  cache.resetBootstrapExpressionProblem = &problem;
  cache.resetBootstrapExpressionTransitions = &transitionByState;
  return cache.resetBootstrapExpressionRelations.get();
}

bool addSupportVars(BoolExpr* expr,
                    std::set<size_t>& support,
                    std::unordered_set<BoolExpr*>& visited,
                    size_t maxSupport) {
  std::vector<BoolExpr*> stack;
  if (expr != nullptr) {
    // LCOV_EXCL_START
    stack.push_back(expr);
    // LCOV_EXCL_STOP
  }
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr || !visited.insert(node).second) {
      continue;
    }
    switch (node->getOp()) {
      case Op::VAR:
        if (node->getId() >= 2) {
          support.insert(node->getId());
          if (support.size() > maxSupport) {
            // LCOV_EXCL_START
            return false;  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
          }
        // LCOV_EXCL_START
        }
        // LCOV_EXCL_STOP
        break;
      case Op::NOT:
        stack.push_back(node->getLeft());
        break;
      case Op::AND:
      case Op::OR:
      case Op::XOR:
        stack.push_back(node->getLeft());
        stack.push_back(node->getRight());
        break;
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        break;  // LCOV_EXCL_LINE
    }
  }
  return true;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

bool addSupportVars(BoolExpr* expr,
                    std::set<size_t>& support,
                    std::unordered_set<BoolExpr*>& visited) {
  return addSupportVars(
      expr, support, visited, kMaxResetSpecializedExpressionSupport);
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
std::optional<std::set<size_t>> collectSupportVars(BoolExpr* expr) {
  std::set<size_t> support;
  std::unordered_set<BoolExpr*> visited;
  if (!addSupportVars(expr, support, visited)) {
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return support;
}

const std::set<size_t>* ResetSymbolicEvaluator::cachedSupportVars(
    // LCOV_EXCL_START
    BoolExpr* expr) {
  if (expr == nullptr) {
  // LCOV_EXCL_STOP
    return nullptr;  // LCOV_EXCL_LINE
  }
  if (const auto it = supportMemo_.find(expr); it != supportMemo_.end()) {
    return &it->second;
  }
  if (supportMisses_.find(expr) != supportMisses_.end()) {
    return nullptr;  // LCOV_EXCL_LINE
  }

  auto support = collectSupportVars(expr);
  if (!support.has_value()) {
    supportMisses_.insert(expr);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return nullptr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  const auto [it, _] = supportMemo_.emplace(expr, std::move(*support));
  return &it->second;
}

struct AffineXorSignature {
  bool constant = false;
  std::vector<size_t> symbols;
// LCOV_EXCL_START
};
// LCOV_EXCL_STOP

std::optional<AffineXorSignature> affineXorSignature(BoolExpr* expr) {
  if (expr == nullptr) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  AffineXorSignature signature;
  std::vector<BoolExpr*> stack{expr};
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    switch (node->getOp()) {
      case Op::VAR: {
        const size_t symbol = node->getId();
        if (symbol == 1) {
          signature.constant = !signature.constant;
        } else if (symbol >= 2) {
          signature.symbols.push_back(symbol);
        }
        break;
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      case Op::NOT:
        // LCOV_EXCL_START
        // In Boolean affine form, NOT(x) is x xor 1.
        // LCOV_EXCL_STOP
        signature.constant = !signature.constant;
        stack.push_back(node->getLeft());
        break;
      case Op::XOR:
        stack.push_back(node->getLeft());
        stack.push_back(node->getRight());
        break;
      case Op::AND:
      case Op::OR:
        return std::nullopt;
      case Op::NONE:  // LCOV_EXCL_LINE
      default:
        return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  std::sort(signature.symbols.begin(), signature.symbols.end());
  std::vector<size_t> oddSymbols;
  oddSymbols.reserve(signature.symbols.size());
  for (size_t i = 0; i < signature.symbols.size();) {
    const size_t symbol = signature.symbols[i];
    size_t count = 0;
    while (i < signature.symbols.size() && signature.symbols[i] == symbol) {
      ++i;
      ++count;
    }
    if ((count & 1U) != 0U) {
      oddSymbols.push_back(symbol);
    }
  }
  signature.symbols = std::move(oddSymbols);
  return signature;
}

std::optional<StateCube> findAffineXorRelationConflict(
    const std::vector<BoolExpr*>& expressions,
    const StateCube& cube) {
  std::vector<std::optional<AffineXorSignature>> signatures;
  signatures.reserve(expressions.size());
  for (BoolExpr* expr : expressions) {
    signatures.push_back(affineXorSignature(expr));
  }

  for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
    if (!signatures[lhs].has_value()) {
      continue;
    }
    // LCOV_EXCL_START
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
    // LCOV_EXCL_STOP
      if (!signatures[rhs].has_value() ||
          signatures[lhs]->symbols != signatures[rhs]->symbols) {
        continue;
      }
      const bool expressionsDiffer =
          signatures[lhs]->constant != signatures[rhs]->constant;
      const bool cubeValuesDiffer = cube[lhs].value != cube[rhs].value;
      if (expressionsDiffer != cubeValuesDiffer) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        // LCOV_EXCL_START
        return conflict;
        // LCOV_EXCL_STOP
      }
    }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  return std::nullopt;
  // LCOV_EXCL_STOP
}

bool supportsIntersect(const std::set<size_t>& lhs, // LCOV_EXCL_LINE
                       const std::set<size_t>& rhs) {
  auto lhsIt = lhs.begin(); // LCOV_EXCL_LINE
  auto rhsIt = rhs.begin(); // LCOV_EXCL_LINE
  while (lhsIt != lhs.end() && rhsIt != rhs.end()) { // LCOV_EXCL_LINE
    if (*lhsIt == *rhsIt) { // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    if (*lhsIt < *rhsIt) { // LCOV_EXCL_LINE
      ++lhsIt;  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      ++rhsIt; // LCOV_EXCL_LINE
    }
  }
  return false; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

size_t supportIntersectionSize(const std::set<size_t>& lhs,
                               const std::set<size_t>& rhs) {
  size_t count = 0;
  auto lhsIt = lhs.begin();
  auto rhsIt = rhs.begin();
  while (lhsIt != lhs.end() && rhsIt != rhs.end()) {
    if (*lhsIt == *rhsIt) {
      ++count;
      ++lhsIt;
      ++rhsIt;
    } else if (*lhsIt < *rhsIt) {
      ++lhsIt;
    } else {
      ++rhsIt;
    }
  }
  return count;
}

std::optional<std::vector<std::pair<BoolExpr*, BoolExpr*>>>
selectRelevantBootstrapEqualityExprs(
    const KInductionProblem& problem,
    ResetSymbolicEvaluator& evaluator,
    std::set<size_t>& relevantSupport,
    ResetExpressionCanonicalizer* canonicalizer = nullptr) {
  struct Candidate { // LCOV_EXCL_LINE
    BoolExpr* lhs = nullptr;
    // LCOV_EXCL_START
    BoolExpr* rhs = nullptr;
    // LCOV_EXCL_STOP
    std::set<size_t> support;
  };

  std::vector<Candidate> candidates;
  if (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
    candidates.reserve(problem.bootstrapStateEqualityPairs.size());
    for (const auto& [lhsSymbol, rhsSymbol] :
         problem.bootstrapStateEqualityPairs) {
      const auto lhsExpr =
          evaluator.stateExpr(lhsSymbol, problem.resetBootstrapCycles); // LCOV_EXCL_LINE
      const auto rhsExpr =
          // LCOV_EXCL_START
          evaluator.stateExpr(rhsSymbol, problem.resetBootstrapCycles);
          // LCOV_EXCL_STOP
      if (!lhsExpr.has_value() || !rhsExpr.has_value()) { // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      BoolExpr* lhs = *lhsExpr;
      // LCOV_EXCL_STOP
      BoolExpr* rhs = *rhsExpr; // LCOV_EXCL_LINE
      if (canonicalizer != nullptr) { // LCOV_EXCL_LINE
        lhs = canonicalizer->canonicalize(lhs); // LCOV_EXCL_LINE
        rhs = canonicalizer->canonicalize(rhs); // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE

      const auto* lhsSupport = evaluator.cachedSupportVars(lhs); // LCOV_EXCL_LINE
      if (lhsSupport == nullptr) { // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      const auto* rhsSupport = evaluator.cachedSupportVars(rhs); // LCOV_EXCL_LINE
      if (rhsSupport == nullptr) { // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      std::set<size_t> support = *lhsSupport; // LCOV_EXCL_LINE
      support.insert(rhsSupport->begin(), rhsSupport->end()); // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      candidates.push_back({lhs, rhs, std::move(support)});
    }
  }

  std::vector<std::pair<BoolExpr*, BoolExpr*>> selected;
  selected.reserve(candidates.size());
  std::vector<bool> used(candidates.size(), false);
  bool changed = true;
  // LCOV_EXCL_STOP
  while (changed) {
    // LCOV_EXCL_START
    changed = false;
    // LCOV_EXCL_STOP
    for (size_t i = 0; i < candidates.size(); ++i) {
      if (used[i] || !supportsIntersect(candidates[i].support, relevantSupport)) { // LCOV_EXCL_LINE
        continue; // LCOV_EXCL_LINE
      }
      used[i] = true;  // LCOV_EXCL_LINE
      changed = true;  // LCOV_EXCL_LINE
      selected.emplace_back(candidates[i].lhs, candidates[i].rhs);  // LCOV_EXCL_LINE
      relevantSupport.insert(  // LCOV_EXCL_LINE
          candidates[i].support.begin(), candidates[i].support.end());  // LCOV_EXCL_LINE
      if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {  // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE
  }

  return selected;
}

std::optional<std::vector<std::pair<BoolExpr*, BoolExpr*>>>
selectRelevantFrameInvariantEqualityExprs(
    BoolExpr* frameInvariant,
    ResetSymbolicEvaluator& evaluator,
    // LCOV_EXCL_START
    size_t targetStep,
    std::set<size_t>& relevantSupport,
    ResetExpressionCanonicalizer* canonicalizer = nullptr) {
  struct Candidate {
  // LCOV_EXCL_STOP
    BoolExpr* lhs = nullptr;
    // LCOV_EXCL_START
    BoolExpr* rhs = nullptr;
    std::set<size_t> support;
  };

  const auto equalityPairs = collectSimpleVariableEqualities(frameInvariant);
  std::vector<Candidate> candidates;
  // LCOV_EXCL_STOP
  candidates.reserve(equalityPairs.size());
  // LCOV_EXCL_START
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    const auto lhsExpr = evaluator.stateExpr(lhsSymbol, targetStep);  // LCOV_EXCL_LINE
    const auto rhsExpr = evaluator.stateExpr(rhsSymbol, targetStep);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (!lhsExpr.has_value() || !rhsExpr.has_value()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    BoolExpr* lhs = *lhsExpr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    BoolExpr* rhs = *rhsExpr;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (canonicalizer != nullptr) {  // LCOV_EXCL_LINE
      lhs = canonicalizer->canonicalize(lhs);  // LCOV_EXCL_LINE
      rhs = canonicalizer->canonicalize(rhs);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP

    const auto* lhsSupport = evaluator.cachedSupportVars(lhs);  // LCOV_EXCL_LINE
    if (lhsSupport == nullptr) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    const auto* rhsSupport = evaluator.cachedSupportVars(rhs);  // LCOV_EXCL_LINE
    if (rhsSupport == nullptr) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    std::set<size_t> support = *lhsSupport;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    support.insert(rhsSupport->begin(), rhsSupport->end());  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    candidates.push_back({lhs, rhs, std::move(support)});  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  std::vector<std::pair<BoolExpr*, BoolExpr*>> selected;
  selected.reserve(candidates.size());
  std::vector<bool> used(candidates.size(), false);
  bool changed = true;
  // LCOV_EXCL_STOP
  while (changed) {
    // LCOV_EXCL_START
    changed = false;
    // LCOV_EXCL_STOP
    for (size_t i = 0; i < candidates.size(); ++i) {
      if (used[i] || !supportsIntersect(candidates[i].support, relevantSupport)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      used[i] = true;  // LCOV_EXCL_LINE
      changed = true;  // LCOV_EXCL_LINE
      selected.emplace_back(candidates[i].lhs, candidates[i].rhs);  // LCOV_EXCL_LINE
      relevantSupport.insert(  // LCOV_EXCL_LINE
          candidates[i].support.begin(), candidates[i].support.end());  // LCOV_EXCL_LINE
      if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {  // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE
  }

  return selected;
}

std::optional<StateCube> resetSpecializedExpressionConflictCube(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    ResetSymbolicEvaluator& evaluator,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant = nullptr,
    std::unordered_map<
        ResetExpressionConflictKey,
        ResetExpressionConflictMemoEntry,
        // LCOV_EXCL_START
        ResetExpressionConflictKeyHash>* memo = nullptr,
        // LCOV_EXCL_STOP
    std::unordered_map<
        ResetFrontierCubeKey,
        size_t,
        ResetFrontierCubeKeyHash>* budgetSkipFromStep = nullptr) {
  ResetExpressionConflictKey memoKey;
  if (memo != nullptr) {
    memoKey = resetExpressionConflictCacheKey(cube, targetStep, frameInvariant);
    // LCOV_EXCL_START
    if (const auto* entry =
            lookupResetExpressionConflictMemo(*memo, memoKey)) {
      if (!entry->hasConflict) {
        return std::nullopt;
        // LCOV_EXCL_STOP
      }
      return entry->conflict;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
  const bool deepResetExpressionStep =
      targetStep >
      problem.resetBootstrapCycles +
          // LCOV_EXCL_START
          kMaxResetSpecializedBadFormulaValidationFrame;
          // LCOV_EXCL_STOP
  if (deepResetExpressionStep && budgetSkipFromStep != nullptr &&
      // LCOV_EXCL_START
      resetExpressionBudgetSkipApplies(  // LCOV_EXCL_LINE
          *budgetSkipFromStep, cube, targetStep, frameInvariant)) {  // LCOV_EXCL_LINE
    if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: reset-specialized expression miss "
          "reason=deep_budget_skip cube=",
          // LCOV_EXCL_STOP
          cube.size(),  // LCOV_EXCL_LINE
          " target_step=",
          targetStep,
          " support=0 initial_equalities=0 bootstrap_equalities=0 "
          "frame_invariant_equalities=0 literals=",
          formatCubeForDiag(cube),  // LCOV_EXCL_LINE
          " hash=",
          cubeFingerprint(cube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (memo != nullptr) {  // LCOV_EXCL_LINE
      rememberResetExpressionConflictMemo(*memo, memoKey, std::nullopt);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  const auto remember = [&](std::optional<StateCube> conflict)
      -> std::optional<StateCube> {
    if (memo != nullptr) {
      if (conflict.has_value()) {
        // LCOV_EXCL_START
        normalizeCube(*conflict);
      }
      rememberResetExpressionConflictMemo(*memo, memoKey, conflict);
    }
    return conflict;
  };
  const auto miss = [&](std::string_view reason,
  // LCOV_EXCL_STOP
                        size_t supportSize = 0,
                        size_t initialEqualityClauses = 0,
                        size_t bootstrapEqualityClauses = 0,
                        size_t frameInvariantEqualityClauses = 0)
      -> std::optional<StateCube> {
    if (deepResetExpressionStep && budgetSkipFromStep != nullptr &&
        (reason == "canonicalize_budget" ||  // LCOV_EXCL_LINE
         reason == "raw_support_cap" ||  // LCOV_EXCL_LINE
         reason == "support_cap" ||  // LCOV_EXCL_LINE
         reason == "encoded_support_cap")) {  // LCOV_EXCL_LINE
      rememberResetExpressionBudgetSkip(  // LCOV_EXCL_LINE
          *budgetSkipFromStep, cube, targetStep, frameInvariant);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression miss reason=",
          reason,
          " cube=",
          cube.size(),
          " target_step=",
          targetStep,
          " support=",
          // LCOV_EXCL_START
          supportSize,
          // LCOV_EXCL_STOP
          " initial_equalities=",
          initialEqualityClauses,
          " bootstrap_equalities=",
          // LCOV_EXCL_START
          bootstrapEqualityClauses,
          // LCOV_EXCL_STOP
          " frame_invariant_equalities=",
          frameInvariantEqualityClauses,
          " literals=",
          formatCubeForDiag(cube),
          " hash=",
          cubeFingerprint(cube));
    }
    // LCOV_EXCL_START
    return remember(std::nullopt);
    // LCOV_EXCL_STOP
  };  // LCOV_EXCL_LINE

  if (problem.resetBootstrapCycles == 0 || cube.empty() ||
      cube.size() > kMaxResetSpecializedExpressionCube) {
    return miss("unsupported_shape");  // LCOV_EXCL_LINE
  }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  std::vector<BoolExpr*> resetExprs;
  resetExprs.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto expr = evaluator.stateExpr(literal.symbol, targetStep);
    if (!expr.has_value()) {
      return miss(evaluator.budgetExhausted() ? "state_expr_budget"  // LCOV_EXCL_LINE
                                              // LCOV_EXCL_START
                                              : "state_expr_missing",
                                              // LCOV_EXCL_STOP
                  0);
    }
    resetExprs.push_back(*expr);
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  if (evaluator.budgetExhausted()) {
    return miss("budget");  // LCOV_EXCL_LINE
  }

  std::set<size_t> rawSupport;
  for (BoolExpr* expr : resetExprs) {
    const auto* support = evaluator.cachedSupportVars(expr);
    if (support == nullptr) {
      return miss("raw_support_cap", rawSupport.size());  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    rawSupport.insert(support->begin(), support->end());
    if (rawSupport.size() > kMaxResetSpecializedExpressionSupport) {
      return miss("raw_support_cap", rawSupport.size());  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
  }

  // Fold frame-0 assignments and SEC initial equality classes before any
  // support budgeting. Without this, two reset cones that differ only by
  // design0/design1 representative names look twice as wide and can hit the
  // ASIC support cap before the local SAT proof gets to see the equalities.
  // LCOV_EXCL_START
  ResetExpressionCanonicalizer canonicalizer(problem);
  if (canonicalizer.inconsistent()) {
    StateCube conflict = cube;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    normalizeCube(conflict);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return remember(conflict);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  size_t canonicalizeBudget = kMaxDeepResetExpressionCanonicalizeNodes;
  std::vector<BoolExpr*> proofExprs;
  proofExprs.reserve(resetExprs.size());
  for (size_t i = 0; i < resetExprs.size(); ++i) {
    // LCOV_EXCL_START
    BoolExpr* canonical = nullptr;
    // LCOV_EXCL_STOP
    if (deepResetExpressionStep) {
      auto bounded =
          canonicalizer.canonicalizeBounded(resetExprs[i], canonicalizeBudget);  // LCOV_EXCL_LINE
      if (!bounded.has_value()) {  // LCOV_EXCL_LINE
        return miss("canonicalize_budget", rawSupport.size());  // LCOV_EXCL_LINE
      }
      canonical = *bounded;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    } else {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      canonical = canonicalizer.canonicalize(resetExprs[i]);
    }
    proofExprs.push_back(canonical);
    // LCOV_EXCL_START
    if (isConstExpr(canonical, !cube[i].value)) {
    // LCOV_EXCL_STOP
      return remember(StateCube{cube[i]});  // LCOV_EXCL_LINE
    }
  }

  std::set<size_t> relevantSupport;
  for (BoolExpr* expr : proofExprs) {
    const auto* support = evaluator.cachedSupportVars(expr);
    if (support == nullptr) {
      return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
    }
    relevantSupport.insert(support->begin(), support->end());
    if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {
      // LCOV_EXCL_START
      return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  const bool canonicalizeEqualityExprs =
      targetStep <=
      problem.resetBootstrapCycles +
          kMaxResetSpecializedBadFormulaValidationFrame;
  ResetExpressionCanonicalizer* equalityCanonicalizer =
      canonicalizeEqualityExprs ? &canonicalizer : nullptr;
  auto bootstrapEqualityExprs =
      selectRelevantBootstrapEqualityExprs(
          problem, evaluator, relevantSupport, equalityCanonicalizer);
  // LCOV_EXCL_START
  if (!bootstrapEqualityExprs.has_value()) {
  // LCOV_EXCL_STOP
    return miss(evaluator.budgetExhausted() ? "bootstrap_eq_budget"  // LCOV_EXCL_LINE
                                            // LCOV_EXCL_START
                                            : "bootstrap_eq_missing",
                                            // LCOV_EXCL_STOP
                relevantSupport.size());  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  auto frameInvariantEqualityExprs =
      selectRelevantFrameInvariantEqualityExprs(
          frameInvariant,
          evaluator,
          targetStep,
          relevantSupport,
          equalityCanonicalizer);
  if (!frameInvariantEqualityExprs.has_value()) {
    return miss(evaluator.budgetExhausted() ? "frame_invariant_eq_budget"  // LCOV_EXCL_LINE
                                            : "frame_invariant_eq_missing",
                relevantSupport.size(),  // LCOV_EXCL_LINE
                0,
                bootstrapEqualityExprs->size());  // LCOV_EXCL_LINE
  }

  // LCOV_EXCL_START
  std::vector<std::pair<BoolExpr*, BoolExpr*>> proofEqualityExprs;
  proofEqualityExprs.reserve(
      bootstrapEqualityExprs->size() + frameInvariantEqualityExprs->size());
      // LCOV_EXCL_STOP
  proofEqualityExprs.insert(
      // LCOV_EXCL_START
      proofEqualityExprs.end(),
      bootstrapEqualityExprs->begin(),
      // LCOV_EXCL_STOP
      bootstrapEqualityExprs->end());
  proofEqualityExprs.insert(
      proofEqualityExprs.end(),
      frameInvariantEqualityExprs->begin(),
      frameInvariantEqualityExprs->end());
  if (proofEqualityExprs.size() >
      // LCOV_EXCL_START
      kMaxResetExpressionProofRewriteEqualities) {
    return miss(  // LCOV_EXCL_LINE
        "proof_equality_cap",  // LCOV_EXCL_LINE
        relevantSupport.size(),  // LCOV_EXCL_LINE
        0,
        bootstrapEqualityExprs->size(),  // LCOV_EXCL_LINE
        frameInvariantEqualityExprs->size());  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  if (!proofEqualityExprs.empty()) {
    // Bootstrap equalities and the validated PDR frame invariant are exact
    // reset-image facts for this target frame.  Quotient candidate expressions
    // through them before SAT so small equality contradictions do not fall into
    // a broad reset-frontier BMC query.
    BoolExprEqualityRewriter proofRewriter;  // LCOV_EXCL_LINE
    proofRewriter.refineToFixedPoint(proofEqualityExprs);  // LCOV_EXCL_LINE
    if (proofRewriter.inconsistent()) {  // LCOV_EXCL_LINE
      StateCube conflict = cube;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return remember(conflict);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    std::vector<BoolExpr*> rewrittenProofExprs;  // LCOV_EXCL_LINE
    rewrittenProofExprs.reserve(proofExprs.size());  // LCOV_EXCL_LINE
    bool changed = false;  // LCOV_EXCL_LINE
    for (size_t i = 0; i < proofExprs.size(); ++i) {  // LCOV_EXCL_LINE
      BoolExpr* rewritten = proofRewriter.rewrite(proofExprs[i]);  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      rewrittenProofExprs.push_back(rewritten);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      changed |= rewritten != proofExprs[i];  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      if (isConstExpr(rewritten, !cube[i].value)) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return remember(StateCube{cube[i]});  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    if (changed) {  // LCOV_EXCL_LINE
      proofExprs = std::move(rewrittenProofExprs);  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      if (const auto conflict =  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              findResetExpressionRelationConflict(proofExprs, cube);  // LCOV_EXCL_LINE
          conflict.has_value()) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: reset-specialized expression conflict cube=",
              // LCOV_EXCL_STOP
              cube.size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              "->",
              // LCOV_EXCL_STOP
              conflict->size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              " via=proof_rewrite hash=",
              // LCOV_EXCL_STOP
              cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }  // LCOV_EXCL_LINE
        return remember(*conflict);  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
      if (const auto conflict =  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              findResetExpressionImplicationConflict(proofExprs, cube);  // LCOV_EXCL_LINE
          conflict.has_value()) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: reset-specialized expression conflict cube=",
              // LCOV_EXCL_STOP
              cube.size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              "->",
              // LCOV_EXCL_STOP
              conflict->size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              " via=proof_rewrite_implication hash=",
              // LCOV_EXCL_STOP
              cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        }  // LCOV_EXCL_LINE
        return remember(*conflict);  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
      if (const auto conflict =  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              findAffineXorRelationConflict(proofExprs, cube);  // LCOV_EXCL_LINE
          conflict.has_value()) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: reset-specialized expression conflict cube=",
              // LCOV_EXCL_STOP
              cube.size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              "->",
              conflict->size(),  // LCOV_EXCL_LINE
              " via=proof_rewrite_affine_xor hash=",
              // LCOV_EXCL_STOP
              cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return remember(*conflict);  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
      relevantSupport.clear();  // LCOV_EXCL_LINE
      for (BoolExpr* expr : proofExprs) {  // LCOV_EXCL_LINE
        const auto* support = evaluator.cachedSupportVars(expr);  // LCOV_EXCL_LINE
        if (support == nullptr) {  // LCOV_EXCL_LINE
          return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
        }
        relevantSupport.insert(support->begin(), support->end());  // LCOV_EXCL_LINE
        if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {  // LCOV_EXCL_LINE
          return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
        }
      }
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  const auto tryPairProbeConflict = [&]() -> std::optional<StateCube> {
    if (cube.size() <= 2 ||
        cube.size() > kMaxResetSpecializedExpressionPairProbeCube) {
      return std::nullopt;
    }

    struct PairProbe {
      size_t lhs = 0;
      size_t rhs = 0;
      size_t supportUnion = 0;
      bool oppositeValues = false;
    };

// LCOV_EXCL_START


// LCOV_EXCL_STOP
    std::vector<std::set<size_t>> expressionSupports(cube.size());
    std::vector<bool> satisfiedConstantExprs(cube.size(), false);
    for (size_t i = 0; i < cube.size(); ++i) {
      // A constant reset expression that already matches the cube literal can
      // never be the reason a two-literal reset-image cube is UNSAT.  Skipping
      // it keeps the bounded pair-probe budget focused on real relations; AES
      // samples showed these zero/one-support constants otherwise displaced
      // the useful small equality pair.
      satisfiedConstantExprs[i] =
          isConstExpr(proofExprs[i], cube[i].value);
      const auto* support = evaluator.cachedSupportVars(proofExprs[i]);
      if (support == nullptr) {
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      expressionSupports[i] = *support;
    }

    std::vector<PairProbe> pairProbes;
    pairProbes.reserve(cube.size() * cube.size() / 2);
    for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
      for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
        if (satisfiedConstantExprs[lhs] || satisfiedConstantExprs[rhs]) {
          continue;
        }
        const size_t shared =
            supportIntersectionSize(expressionSupports[lhs], expressionSupports[rhs]);
        const size_t supportUnion =
            expressionSupports[lhs].size() + expressionSupports[rhs].size() -
            shared;
        if (supportUnion > kMaxResetSpecializedExpressionPairProbeSupport) {
          continue;
        }
        pairProbes.push_back(
            {lhs,
             rhs,
             supportUnion,
             cube[lhs].value != cube[rhs].value});
      }
    }
    std::sort(
        pairProbes.begin(),
        pairProbes.end(),
        [](const PairProbe& lhs, const PairProbe& rhs) {
          if (lhs.supportUnion != rhs.supportUnion) {
            return lhs.supportUnion < rhs.supportUnion;
          }
          // Samples on AES showed wide opposite-polarity pairs can be SAT and
          // expensive.  Prefer the smallest reset-image proof first; polarity
          // only breaks ties between equally local probes.
          if (lhs.oppositeValues != rhs.oppositeValues) {
            return lhs.oppositeValues;
          }
          if (lhs.lhs != rhs.lhs) {
            return lhs.lhs < rhs.lhs;
          }
          return lhs.rhs < rhs.rhs;
        });

    size_t attemptedPairProbes = 0;
    for (const auto& probe : pairProbes) {
      if (attemptedPairProbes++ >=
          kMaxResetSpecializedExpressionPairProbes) {
        break;
      }
      StateCube candidate{cube[probe.lhs], cube[probe.rhs]};
      normalizeCube(candidate);
      const auto pairConflict =
          resetSpecializedExpressionConflictCube(
              problem,
              transitionByState,
              evaluator,
              candidate,
              targetStep,
              frameInvariant,
              memo,
              budgetSkipFromStep);
      if (pairConflict.has_value() && pairConflict->size() < cube.size()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              cube.size(),
              "->",
              pairConflict->size(),
              " via=pair_probe support=",
              probe.supportUnion,
              " hash=",
              cubeFingerprint(*pairConflict));
        }
        return remember(*pairConflict);
      }
    }
    return std::nullopt;
  };

  // For tiny root cubes, first prove a two-literal reset conflict. AES
  // samples showed neighboring four-literal cubes differing by one valuation:
  // learning the full cube made PDR rediscover the neighbor, while an UNSAT
  // pair proof blocked both. Each pair probe is still a complete SAT proof over
  // the selected reset-image constraints; if no pair is proved UNSAT we fall
  // through to the full cube proof below.
  if (const auto pairConflict = tryPairProbeConflict();
      pairConflict.has_value()) {
    return pairConflict;
  }

  const auto tryTripleProbeConflict = [&]() -> std::optional<StateCube> {
    if (cube.size() <= 3 ||
        cube.size() > kMaxResetSpecializedExpressionPairProbeCube) {
      return std::nullopt;
    }

    struct TripleProbe {
      // LCOV_EXCL_START
      size_t first = 0;
      // LCOV_EXCL_STOP
      size_t second = 0;
      size_t third = 0;
      size_t supportUnion = 0;
    };

    std::vector<std::set<size_t>> expressionSupports(cube.size());
    std::vector<bool> satisfiedConstantExprs(cube.size(), false);
    for (size_t i = 0; i < cube.size(); ++i) {
      satisfiedConstantExprs[i] =
          isConstExpr(proofExprs[i], cube[i].value);
      const auto* support = evaluator.cachedSupportVars(proofExprs[i]);
      if (support == nullptr) {
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      expressionSupports[i] = *support;
    }

    auto supportUnionSize = [&](size_t first, size_t second, size_t third) {
      std::set<size_t> unionSupport = expressionSupports[first];
      unionSupport.insert(
          // LCOV_EXCL_START
          expressionSupports[second].begin(), expressionSupports[second].end());
          // LCOV_EXCL_STOP
      unionSupport.insert(
          expressionSupports[third].begin(), expressionSupports[third].end());
      return unionSupport.size();
    // LCOV_EXCL_START
    };
    // LCOV_EXCL_STOP

    std::vector<TripleProbe> tripleProbes;
    for (size_t first = 0; first < cube.size(); ++first) {
      if (satisfiedConstantExprs[first]) {
        continue;
      }
      for (size_t second = first + 1; second < cube.size(); ++second) {
        if (satisfiedConstantExprs[second]) {
          continue;  // LCOV_EXCL_LINE
        }
        for (size_t third = second + 1; third < cube.size(); ++third) {
          if (satisfiedConstantExprs[third]) {
            continue;  // LCOV_EXCL_LINE
          }
          const size_t supportUnion =
              supportUnionSize(first, second, third);
          if (supportUnion > kMaxResetSpecializedExpressionTripleProbeSupport) {
            continue;
          }
          tripleProbes.push_back({first, second, third, supportUnion});
        }
      }
    }
    // LCOV_EXCL_START
    std::sort(
    // LCOV_EXCL_STOP
        tripleProbes.begin(),
        tripleProbes.end(),
        [](const TripleProbe& lhs, const TripleProbe& rhs) {
          if (lhs.supportUnion != rhs.supportUnion) {
            return lhs.supportUnion < rhs.supportUnion;
          }
          // LCOV_EXCL_START
          if (lhs.first != rhs.first) {
          // LCOV_EXCL_STOP
            return lhs.first < rhs.first;
          }
          if (lhs.second != rhs.second) {
            return lhs.second < rhs.second;
          }
          return lhs.third < rhs.third;  // LCOV_EXCL_LINE
        });

    size_t attemptedTripleProbes = 0;
    for (const auto& probe : tripleProbes) {
      if (attemptedTripleProbes++ >=
          kMaxResetSpecializedExpressionTripleProbes) {
        break;  // LCOV_EXCL_LINE
      }
      StateCube candidate{
          cube[probe.first], cube[probe.second], cube[probe.third]};
      normalizeCube(candidate);
      const auto tripleConflict =
          resetSpecializedExpressionConflictCube(
              problem,
              transitionByState,
              evaluator,
              candidate,
              targetStep,
              frameInvariant,
              memo,
              budgetSkipFromStep);
      if (tripleConflict.has_value() && tripleConflict->size() < cube.size()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              cube.size(),
              "->",
              tripleConflict->size(),
              " via=triple_probe support=",
              probe.supportUnion,
              " hash=",
              cubeFingerprint(*tripleConflict));
        }
        return remember(*tripleConflict);
      }
    }
    return std::nullopt;
  };

  // Some ASIC reset-image contradictions are genuinely relational across
  // three literals: every pair is satisfiable, but the triple is not.  Probe a
  // few smallest-support triples before opening the full cube SAT query, which
  // AES sampling showed can jump to a 900+ symbol support and dominate PDR.
  if (const auto tripleConflict = tryTripleProbeConflict();
      tripleConflict.has_value()) {
    return tripleConflict;
  }

  const size_t fullSatSupportCap =
      cube.size() <= 3
          ? kMaxResetSpecializedExpressionSmallCubeFullSatSupport
          : kMaxResetSpecializedExpressionFullSatSupport;
  if (relevantSupport.size() > fullSatSupportCap) {
    return miss("full_sat_support_cap", relevantSupport.size());
  }

  // This is a reset-image proof over the substituted cube expressions only.
  // It is strictly an over-approximation when a transition is missing because
  // the symbolic evaluator leaves that state bit as a free variable. Therefore
  // UNSAT here is a sound reset-frontier conflict, while SAT merely falls back
  // to the exact concrete reset unroll below.
  // This shortcut performs one reset-image UNSAT query. AES sampling showed
  // assumption solving spending minutes here just to recover a smaller
  // failed-assumption core, so keep the proof as a Kissat one-shot query and
  // learn the full cube when the query is UNSAT.
  SATSolverWrapper solver(KEPLER_FORMAL::Config::SolverType::KISSAT);
  solver.configureForSecResetExpressionProof(problem.allSymbols.size());
  if (pdrResetShortcutDiagEnabled()) {
    emitSecDiag(
        "SEC PDR stats: reset-specialized expression solver_profile=reset_expression");
  }
  std::unordered_map<size_t, int> leafLits;
  leafLits.reserve(relevantSupport.size());

  FrameFormulaEncoder encoder(
      solver,
      // LCOV_EXCL_START
      leafLits,
      // LCOV_EXCL_STOP
      /*createMissingLeaves=*/true,
      // LCOV_EXCL_START
      std::max(
          leafLits.size() * 4 + proofExprs.size(),
          proofExprs.size() * static_cast<size_t>(256)));
          // LCOV_EXCL_STOP

  // The expressions were already rewritten through initial assignments and
  // LCOV_EXCL_START
  // equality classes, so do not add the original equality-pair endpoints back
  // LCOV_EXCL_STOP
  // into this local proof. Doing so recreates the sampled AES support blow-up.
  // LCOV_EXCL_START
  size_t initialEqualityClauses = 0;
  size_t bootstrapEqualityClauses = 0;
  size_t frameInvariantEqualityClauses = 0;
  // LCOV_EXCL_STOP
  for (const auto& [lhsExpr, rhsExpr] : *bootstrapEqualityExprs) {
    addLiteralEquivalence(  // LCOV_EXCL_LINE
        solver,
        encoder.encode(lhsExpr),  // LCOV_EXCL_LINE
        encoder.encode(rhsExpr));  // LCOV_EXCL_LINE
    ++bootstrapEqualityClauses;  // LCOV_EXCL_LINE
  }
  for (const auto& [lhsExpr, rhsExpr] : *frameInvariantEqualityExprs) {
    addLiteralEquivalence(  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        solver,
        encoder.encode(lhsExpr),  // LCOV_EXCL_LINE
        encoder.encode(rhsExpr));  // LCOV_EXCL_LINE
    ++frameInvariantEqualityClauses;  // LCOV_EXCL_LINE
  }


// LCOV_EXCL_STOP
  for (size_t i = 0; i < cube.size(); ++i) {
    const int lit = encoder.encode(proofExprs[i]);
    const int assumption = cube[i].value ? lit : -lit;
    solver.addClause({assumption});
  }
  const size_t encodedSupportSize = encoder.leafLits().size();
  if (encodedSupportSize > kMaxResetSpecializedExpressionSupport) {
    return miss(  // LCOV_EXCL_LINE
        "encoded_support_cap",  // LCOV_EXCL_LINE
        encodedSupportSize,  // LCOV_EXCL_LINE
        initialEqualityClauses,  // LCOV_EXCL_LINE
        bootstrapEqualityClauses,  // LCOV_EXCL_LINE
        frameInvariantEqualityClauses);  // LCOV_EXCL_LINE
  }

  if (pdrResetShortcutDiagEnabled()) {
    emitSecDiag(
        "SEC PDR stats: reset-specialized expression solve cube=",
        cube.size(),
        " target_step=",
        targetStep,
        " support=",
        encodedSupportSize,
        " initial_equalities=",
        initialEqualityClauses,
        " bootstrap_equalities=",
        bootstrapEqualityClauses,
        " frame_invariant_equalities=",
        frameInvariantEqualityClauses,
        " literals=",
        formatCubeForDiag(cube),
        " hash=",
        cubeFingerprint(cube));
  }

  const auto solveStatus = solver.solveWithKissatResourceLimits(
      resetExpressionProofConflictLimit());
  if (solveStatus == SATSolverWrapper::SolveStatus::Unknown) {
    return miss("solver_resource_limit",
                encodedSupportSize,
                initialEqualityClauses,
                bootstrapEqualityClauses,
                frameInvariantEqualityClauses);
  }
  if (solveStatus == SATSolverWrapper::SolveStatus::Sat) {
    return miss("sat",
                encodedSupportSize,
                initialEqualityClauses,
                bootstrapEqualityClauses,
                frameInvariantEqualityClauses);
  }

  StateCube conflict = cube;
  normalizeCube(conflict);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: reset-specialized expression conflict cube=",
        cube.size(),
        "->",
        conflict.size(),
        " support=",
        encodedSupportSize,
        " hash=",
        cubeFingerprint(conflict));
  }
  return remember(conflict);
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

std::optional<StateCube> resetSpecializedConflictCubeAtStep(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    ResetFrontierCache& cache,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant = nullptr,
    bool allowDeepSmallCubeRelaxedBudget = true) {
  // LCOV_EXCL_START
  StateCube queryCube = cube;
  // LCOV_EXCL_STOP
  normalizeCube(queryCube);
  if (problem.resetBootstrapCycles == 0 || queryCube.empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const ResetExpressionConflictKey memoKey =
      resetExpressionConflictCacheKey(queryCube, targetStep, frameInvariant);
  // LCOV_EXCL_START
  if (const auto* entry =
          lookupResetExpressionConflictMemo(
          // LCOV_EXCL_STOP
              cache.resetExpressionConflictByKey, memoKey)) {
    // LCOV_EXCL_START
    if (!entry->hasConflict) {
      return std::nullopt;
    }
    return entry->conflict;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  const bool deepTargetStep =
      // LCOV_EXCL_START
      targetStep >
      // LCOV_EXCL_STOP
      problem.resetBootstrapCycles +
          kMaxResetSpecializedBadFormulaValidationFrame;
  if (deepTargetStep &&
      resetExpressionBudgetSkipApplies(  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          cache.resetExpressionBudgetSkipFromStep,
          // LCOV_EXCL_STOP
          queryCube,
          // LCOV_EXCL_START
          targetStep,
          frameInvariant)) {
    if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: reset-specialized expression miss "
          // LCOV_EXCL_STOP
          "reason=deep_budget_skip cube=",
          queryCube.size(),  // LCOV_EXCL_LINE
          " target_step=",
          targetStep,
          " support=0 initial_equalities=0 bootstrap_equalities=0 "
          "frame_invariant_equalities=0 literals=",
          formatCubeForDiag(queryCube),  // LCOV_EXCL_LINE
          " hash=",
          cubeFingerprint(queryCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    rememberResetExpressionConflictMemo(  // LCOV_EXCL_LINE
        cache.resetExpressionConflictByKey, memoKey, std::nullopt);  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const auto remember = [&](std::optional<StateCube> conflict)
      -> std::optional<StateCube> {
    if (conflict.has_value()) {
      normalizeCube(*conflict);
    }
    // LCOV_EXCL_START
    rememberResetExpressionConflictMemo(
        cache.resetExpressionConflictByKey, memoKey, conflict);
        // LCOV_EXCL_STOP
    return conflict;
  // LCOV_EXCL_START
  };
  // LCOV_EXCL_STOP

  ResetSymbolicEvaluator& evaluator =
      resetSymbolicEvaluatorFor(cache, problem, transitionByState);
  const bool useDeepSmallCubeBudget =
      allowDeepSmallCubeRelaxedBudget &&
      queryCube.size() <= kMaxDeepSmallCubeResetSymbolicLiterals &&
      deepTargetStep;
  const bool useLargeDualRailSmallCubeBudget =
      useDeepSmallCubeBudget &&
      hasLargeDualRailResetFrontierSurface(problem);
  const size_t deepStateLimit =
      useLargeDualRailSmallCubeBudget
          ? kMaxDeepLargeDualRailResetSymbolicEvaluatorStates
          : kMaxDeepSmallCubeResetSymbolicEvaluatorStates;
  const size_t deepExprLimit =
      useLargeDualRailSmallCubeBudget
          ? kMaxDeepLargeDualRailResetSymbolicEvaluatorExprs
          : kMaxDeepSmallCubeResetSymbolicEvaluatorExprs;
  // LCOV_EXCL_START
  std::optional<ScopedResetSymbolicEvaluatorBudget> scopedBudget;
  if (useDeepSmallCubeBudget) {
    if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          "SEC PDR stats: reset-specialized expression relaxed_budget cube=",
          queryCube.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " target_step=",
          // LCOV_EXCL_STOP
          targetStep,
          " state_limit=",
          deepStateLimit,
          " expr_limit=",
          deepExprLimit,
          // LCOV_EXCL_START
          " hash=",
          cubeFingerprint(queryCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    scopedBudget.emplace(  // LCOV_EXCL_LINE
        evaluator,  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        deepStateLimit,
        // LCOV_EXCL_START
        deepExprLimit);
  }  // LCOV_EXCL_LINE
  std::vector<BoolExpr*> resetExprs;
  resetExprs.reserve(queryCube.size());
  // LCOV_EXCL_STOP
  for (const auto& literal : queryCube) {
    const auto expr = evaluator.stateExpr(literal.symbol, targetStep);
    if (!expr.has_value()) {
      return remember(  // LCOV_EXCL_LINE
          resetSpecializedExpressionConflictCube(  // LCOV_EXCL_LINE
              problem,  // LCOV_EXCL_LINE
              transitionByState,  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              evaluator,  // LCOV_EXCL_LINE
              queryCube,
              targetStep,  // LCOV_EXCL_LINE
              frameInvariant,  // LCOV_EXCL_LINE
              &cache.resetExpressionConflictByKey,  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
              &cache.resetExpressionBudgetSkipFromStep));  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    resetExprs.push_back(*expr);
    if (isConstExpr(*expr, !literal.value)) {
      return remember(StateCube{literal});
      // LCOV_EXCL_STOP
    }
  }
  if (evaluator.budgetExhausted()) {
    return remember(  // LCOV_EXCL_LINE
        resetSpecializedExpressionConflictCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            evaluator,  // LCOV_EXCL_LINE
            queryCube,
            targetStep,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            frameInvariant,  // LCOV_EXCL_LINE
            &cache.resetExpressionConflictByKey,  // LCOV_EXCL_LINE
            &cache.resetExpressionBudgetSkipFromStep));  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_STOP

  if (const auto conflict =
          findResetExpressionRelationConflict(resetExprs, queryCube);
      conflict.has_value()) {
    return remember(*conflict);
  }

  // LCOV_EXCL_START
  auto& canonicalizer = resetExpressionCanonicalizerFor(cache, problem);
  if (canonicalizer.inconsistent()) {
    StateCube conflict = queryCube;  // LCOV_EXCL_LINE
    normalizeCube(conflict);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    return remember(conflict);  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }  // LCOV_EXCL_LINE
  std::vector<BoolExpr*> canonicalExprs;
  canonicalExprs.reserve(resetExprs.size());
  size_t canonicalizeBudget = kMaxDeepResetExpressionCanonicalizeNodes;
  // LCOV_EXCL_STOP
  for (size_t i = 0; i < resetExprs.size(); ++i) {
    BoolExpr* canonical = nullptr;
    // LCOV_EXCL_START
    if (useDeepSmallCubeBudget) {
    // LCOV_EXCL_STOP
      auto bounded =
          canonicalizer.canonicalizeBounded(resetExprs[i], canonicalizeBudget);  // LCOV_EXCL_LINE
      if (!bounded.has_value()) {  // LCOV_EXCL_LINE
        rememberResetExpressionBudgetSkip(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            cache.resetExpressionBudgetSkipFromStep,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            queryCube,
            // LCOV_EXCL_START
            targetStep,  // LCOV_EXCL_LINE
            frameInvariant);  // LCOV_EXCL_LINE
        if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          emitSecDiag(  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              "SEC PDR stats: reset-specialized expression miss "
              "reason=canonicalize_budget cube=",
              // LCOV_EXCL_STOP
              queryCube.size(),  // LCOV_EXCL_LINE
              " target_step=",
              targetStep,
              " support=0 initial_equalities=0 bootstrap_equalities=0 "
              // LCOV_EXCL_START
              "frame_invariant_equalities=0 literals=",
              // LCOV_EXCL_STOP
              formatCubeForDiag(queryCube),  // LCOV_EXCL_LINE
              " hash=",
              cubeFingerprint(queryCube));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return remember(std::nullopt);  // LCOV_EXCL_LINE
      }
      canonical = *bounded;  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      canonical = canonicalizer.canonicalize(resetExprs[i]);
    }
    canonicalExprs.push_back(canonical);
    if (isConstExpr(canonical, !queryCube[i].value)) {
      return remember(StateCube{queryCube[i]});  // LCOV_EXCL_LINE
    }
  }
  if (const auto conflict =
          findResetExpressionRelationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {
      // LCOV_EXCL_START
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression conflict cube=",
          // LCOV_EXCL_STOP
          queryCube.size(),
          // LCOV_EXCL_START
          "->",
          // LCOV_EXCL_STOP
          conflict->size(),
          // LCOV_EXCL_START
          " via=canonical hash=",
          // LCOV_EXCL_STOP
          cubeFingerprint(*conflict));
    // LCOV_EXCL_START
    }
    return remember(*conflict);
  }
  // LCOV_EXCL_STOP
  if (const auto conflict =
          findResetExpressionImplicationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: reset-specialized expression conflict cube=",
          queryCube.size(),  // LCOV_EXCL_LINE
          "->",
          conflict->size(),  // LCOV_EXCL_LINE
          " via=implication hash=",
          cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return remember(*conflict);  // LCOV_EXCL_LINE
  }
  if (const auto conflict =
          findAffineXorRelationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          // LCOV_EXCL_START
          "SEC PDR stats: reset-specialized expression conflict cube=",
          queryCube.size(),
          "->",
          conflict->size(),
          // LCOV_EXCL_STOP
          " via=affine_xor hash=",
          // LCOV_EXCL_START
          cubeFingerprint(*conflict));
    }
    return remember(*conflict);
  }
  // LCOV_EXCL_STOP

  auto* bootstrapRelations = resetBootstrapExpressionRelationsFor(
      cache, problem, transitionByState, evaluator, canonicalizer);
  if (bootstrapRelations == nullptr) {
    return resetSpecializedExpressionConflictCube(  // LCOV_EXCL_LINE
        problem,  // LCOV_EXCL_LINE
        transitionByState,  // LCOV_EXCL_LINE
        evaluator,  // LCOV_EXCL_LINE
        queryCube,
        targetStep,  // LCOV_EXCL_LINE
        frameInvariant,  // LCOV_EXCL_LINE
        &cache.resetExpressionConflictByKey,  // LCOV_EXCL_LINE
        &cache.resetExpressionBudgetSkipFromStep);  // LCOV_EXCL_LINE
  }
  if (bootstrapRelations->hasRelation) {
    if (const auto conflict =
            findResetExpressionRelationConflict(
                canonicalExprs, queryCube, &bootstrapRelations->index);
        conflict.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: reset-specialized expression conflict cube=",
            queryCube.size(),
            "->",
            conflict->size(),
            // LCOV_EXCL_START
            " via=bootstrap_relation hash=",
            cubeFingerprint(*conflict));
      }
      return remember(*conflict);
      // LCOV_EXCL_STOP
    }

    // Direct bootstrap equality detects only whole-expression matches.  For
    // local equality sets, quotient candidate expressions through bootstrap
    // relations before opening the optional SAT proof.  Large ASIC equality
    // sets skip this optional rewrite and keep the already-sound index/SAT
    // fallback, because sampling showed the rewrite itself becoming the wall.
    if (bootstrapRelations->hasRewriter &&
        bootstrapRelations->rewriter.inconsistent()) {
      StateCube conflict = queryCube;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return remember(conflict);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    std::vector<BoolExpr*> rewrittenExprs;
    rewrittenExprs.reserve(canonicalExprs.size());
    bool changed = false;
    if (bootstrapRelations->hasRewriter) {
      for (size_t i = 0; i < canonicalExprs.size(); ++i) {
        BoolExpr* rewritten =
            bootstrapRelations->rewriter.rewrite(canonicalExprs[i]);
        rewrittenExprs.push_back(rewritten);
        changed |= rewritten != canonicalExprs[i];
        if (isConstExpr(rewritten, !queryCube[i].value)) {
          return remember(StateCube{queryCube[i]});  // LCOV_EXCL_LINE
        }
      }
    }
    if (changed) {
      if (const auto conflict =
              findResetExpressionRelationConflict(rewrittenExprs, queryCube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              queryCube.size(),
              "->",
              conflict->size(),
              " via=bootstrap_rewrite hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
      if (const auto conflict =
              // LCOV_EXCL_START
              findResetExpressionImplicationConflict(rewrittenExprs, queryCube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              // LCOV_EXCL_STOP
              queryCube.size(),
              // LCOV_EXCL_START
              "->",
              // LCOV_EXCL_STOP
              conflict->size(),
              // LCOV_EXCL_START
              " via=bootstrap_rewrite_implication hash=",
              // LCOV_EXCL_STOP
              cubeFingerprint(*conflict));
        // LCOV_EXCL_START
        }
        return remember(*conflict);
      }
      // LCOV_EXCL_STOP
      if (const auto conflict =  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              findAffineXorRelationConflict(rewrittenExprs, queryCube);  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
          conflict.has_value()) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: reset-specialized expression conflict cube=",
              queryCube.size(),  // LCOV_EXCL_LINE
              "->",
              conflict->size(),  // LCOV_EXCL_LINE
              " via=bootstrap_rewrite_affine_xor hash=",
              cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return remember(*conflict);  // LCOV_EXCL_LINE
      }
    }  // LCOV_EXCL_LINE
  }
  return remember(
      resetSpecializedExpressionConflictCube(
          problem,
          transitionByState,
          evaluator,
          queryCube,
          targetStep,
          frameInvariant,
          &cache.resetExpressionConflictByKey,
          &cache.resetExpressionBudgetSkipFromStep));
}

std::optional<StateCube> resetSpecializedConflictCube(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    ResetFrontierCache& cache,
    const StateCube& cube) {
  return resetSpecializedConflictCubeAtStep(
      problem,
      transitionByState,
      cache,
      cube,
      problem.resetBootstrapCycles);
}

void addSupportSymbols(const std::set<size_t>& support,
                       std::unordered_set<size_t>& symbols) {
  for (const auto symbol : support) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
}

void addStateSupportSymbols(const std::set<size_t>& support,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output) {
  for (const auto symbol : support) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addFormulaSymbols(BoolExpr* formula,
                       std::unordered_set<size_t>& symbols,
                       PdrFormulaSupportCache* supportCache) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  if (supportCache != nullptr) {
    addSupportSymbols(supportCache->support(formula), symbols);
    return;
  }
  addSupportSymbols(formula->getSupportVars(), symbols);
}

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output,
                            PdrFormulaSupportCache& supportCache) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  addStateSupportSymbols(supportCache.support(formula), stateSymbols, output);
}

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist =
      detail::makePdrClosureWorklist(symbols);
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto partnerIt =
        complementPartners.partnersBySymbol.find(worklist[cursor]);
    if (partnerIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    for (const auto partnerSymbol : partnerIt->second) {
      // LCOV_EXCL_START
      if (symbols.insert(partnerSymbol).second) {
        worklist.push_back(partnerSymbol);
      }
      // LCOV_EXCL_STOP
    }
  }
}

void addRelevantComplementedStatePartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (symbols.find(primarySymbol) != symbols.end() || // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        symbols.find(complementedSymbol) != symbols.end()) {
      symbols.insert(primarySymbol);  // LCOV_EXCL_LINE
      symbols.insert(complementedSymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }
}

void addRelevantStateEqualityPartners(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    std::unordered_set<size_t>& symbols) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      const bool lhsNeeded = symbols.find(lhsSymbol) != symbols.end();
      const bool rhsNeeded = symbols.find(rhsSymbol) != symbols.end();
      if (!lhsNeeded && !rhsNeeded) {
        continue;
      }
      changed |= symbols.insert(lhsSymbol).second;
      changed |= symbols.insert(rhsSymbol).second;
    }
  }
}

void addRelevantSameFrameStateEqualityPartners(
    const KInductionProblem& problem,
    std::unordered_set<size_t>& symbols) {
  addRelevantStateEqualityPartners(problem.sameFrameStateEqualityPairs0, symbols);
  addRelevantStateEqualityPartners(problem.sameFrameStateEqualityPairs1, symbols);
}

void addRelevantDualRailPartners(
    const std::vector<DualRailSymbolPair>& railPairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& rails : railPairs) {
    if (symbols.find(rails.mayBeOne) != symbols.end() ||
        symbols.find(rails.mayBeZero) != symbols.end()) {
      symbols.insert(rails.mayBeOne);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      symbols.insert(rails.mayBeZero);
      // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }
}

void addRelevantDualRailPartners(
    PdrFormulaSupportCache* supportCache,
    const std::vector<DualRailSymbolPair>& railPairs,
    std::unordered_set<size_t>& symbols) {
  if (supportCache != nullptr) {
    supportCache->addRelevantDualRailPartners(symbols);
    return;
  }
  addRelevantDualRailPartners(railPairs, symbols);  // LCOV_EXCL_LINE
}

const std::vector<std::pair<size_t, size_t>>& emptySymbolPairs();

bool hasStructuredInitFacts(const KInductionProblem& problem) {
  if (problem.resetBootstrapCycles != 0) {
    return !problem.bootstrapStateAssignments.empty() ||
           (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence() &&
            !problem.bootstrapStateEqualityPairs.empty());
  }
  return !problem.initialStateAssignments.empty() ||
         (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence() &&
          !problem.initialStateEqualityPairs.empty());
}

void addRelevantInitConstraintSymbols(const KInductionProblem& problem,
                                      std::unordered_set<size_t>& symbols) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;

  for (const auto& [symbol, /*value*/ _] : assignments) {
    if (symbols.find(symbol) != symbols.end()) {
      symbols.insert(symbol);
    }
  }
  if (KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
    const auto& equalities = usesBootstrapFrontier
                                 ? problem.bootstrapStateEqualityPairs
                                 : problem.initialStateEqualityPairs;
    for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
      const bool touchesQuery =
          symbols.find(lhsSymbol) != symbols.end() ||
          symbols.find(rhsSymbol) != symbols.end();
      if (!touchesQuery) {
        continue;
      }
      symbols.insert(lhsSymbol);
      symbols.insert(rhsSymbol);
    }
  }
}

void addCubeSymbols(const StateCube& cube, std::unordered_set<size_t>& symbols) {
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
}

void addClauseSymbols(const StateClause& clause, std::unordered_set<size_t>& symbols) {
  for (const auto& literal : clause) {
    symbols.insert(literal.symbol);
  }
}

void ensureFrameClauseIndex(const FrameClauses& frame) {
  if (!frame.clauseIndexDirty) {
    return;
  }

  frame.clauseIndicesBySymbol.clear();
  for (size_t clauseIndex = 0; clauseIndex < frame.clauses.size(); ++clauseIndex) {
    for (const auto& literal : frame.clauses[clauseIndex]) {
      frame.clauseIndicesBySymbol[literal.symbol].push_back(clauseIndex);
    }
  }
  frame.clauseIndexDirty = false;
}

void addAllFrameClauseSymbols(const FrameClauses& frame,
                              std::unordered_set<size_t>& symbols) {
  for (const auto& clause : frame.clauses) {
    addClauseSymbols(clause, symbols);
  }
}

void addRelevantFrameClauseSymbols(const KInductionProblem& problem,
                                   const FrameClauses& frame,
                                   std::unordered_set<size_t>& symbols) {
  // Learned frame clauses are independent constraints.  Clauses outside the
  // current query cone may be omitted soundly, but once a relevant clause pulls
  // in a new symbol, clauses on that symbol can also be needed to avoid
  // repeatedly rediscovering states that are already blocked by the small
  // learned frame.  Close this relation to a bounded fixed point: exact for
  // small local frames, still capped for very large ASIC frames.
  (void)problem;
  ensureFrameClauseIndex(frame);
  const uint64_t emitEpoch = nextClauseEmitEpoch(frame);
  std::vector<size_t> worklist =
      detail::makeDeterministicPdrWorklist(symbols);
  size_t includedClauses = 0;
  size_t includedLiterals = 0;
  const size_t maxProjectedFrameClauses = maxProjectedFrameClausesPerQuery();
  const size_t maxProjectedFrameLiterals = maxProjectedFrameLiteralsPerQuery();
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto symbol = worklist[cursor];
    const auto indexIt = frame.clauseIndicesBySymbol.find(symbol);
    if (indexIt == frame.clauseIndicesBySymbol.end()) {
      continue;
    }
    // LCOV_EXCL_START
    for (const auto clauseIndex : indexIt->second) {
      if (includedClauses >= maxProjectedFrameClauses ||
      // LCOV_EXCL_STOP
          includedLiterals >= maxProjectedFrameLiterals) {
        return;
      }
      if (frame.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
        continue;
      }
      const auto& clause = frame.clauses[clauseIndex];
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;  // LCOV_EXCL_LINE
      }
      if (includedLiterals + clause.size() > maxProjectedFrameLiterals &&
          includedClauses != 0) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      frame.clauseEmitEpochByIndex[clauseIndex] = emitEpoch;
      ++includedClauses;
      includedLiterals += clause.size();
      for (const auto& literal : clause) {
        if (symbols.insert(literal.symbol).second) {
          worklist.push_back(literal.symbol);
        }
      }
    }
  }
}

void addFrameConstraintSymbols(const KInductionProblem& problem,
                               BoolExpr* initFormula,
                               BoolExpr* frameInvariant,
                               const std::vector<FrameClauses>& frames,
                               size_t level,
                               bool exactFrameClauses,
                               const ComplementPartnerIndex& complementPartners,
                               std::unordered_set<size_t>& symbols,
                               PdrFormulaSupportCache* supportCache) {
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Keep Init cone-local even in the exact frame-clause retry. ASIC SEC
      // startup frontiers contain tens of thousands of equality facts, while a
      // predecessor query usually touches only a few of them. The exact retry
      // below disables learned-frame filtering, not this structured Init
      // sparsification.
      addRelevantInitConstraintSymbols(problem, symbols);
    } else {
      addFormulaSymbols(initFormula, symbols, supportCache);
    }
    if (problem.resetBootstrapCycles != 0 && problem.property != nullptr) {
      // PDREngine::run validates the concrete reset/bootstrap F[0] frontier
      // before any PDR query can use it.  The checked safety property is then
      // a real F[0] fact, even when structured init encoding is used instead
      // of the monolithic initFormula.
      addFormulaSymbols(problem.property, symbols, supportCache);
    }
    // Reset-bootstrap refinement clauses live in F[0]. Include their symbols
    // only when they touch the current query cone. ASIC PDR can learn many F[0]
    // CEGAR clauses; encoding all of them in every local predecessor query
    // turns unrelated output slices into a monolithic proof.
    if (exactFrameClauses) {
      addAllFrameClauseSymbols(frames[0], symbols);
    } else {
      addRelevantFrameClauseSymbols(problem, frames[0], symbols);
    }
  } else {
    addFormulaSymbols(frameInvariant, symbols, supportCache);
    if (exactFrameClauses) {
      addAllFrameClauseSymbols(frames[level], symbols);
    } else {
      addRelevantFrameClauseSymbols(problem, frames[level], symbols);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
}

std::vector<size_t> findBadQuerySymbols(const KInductionProblem& problem,
                                        BoolExpr* initFormula,
                                        BoolExpr* frameInvariant,
                                        const std::vector<FrameClauses>& frames,
                                        BoolExpr* badFormula,
                                        size_t level,
                                        const ComplementPartnerIndex& complementPartners,
                                        bool exactFrameClauses,
                                        PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(badFormula, symbols, supportCache);
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      exactFrameClauses,
      complementPartners,
      symbols,
      supportCache);
  return sortUniqueSymbols(std::move(symbols));
}

void addCurrentFramePartnerClosure(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols,
    PdrFormulaSupportCache* supportCache) {
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
}

std::vector<size_t> sortClosedCurrentFrameSymbols(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t> symbols,
    PdrFormulaSupportCache* supportCache) {
  addCurrentFramePartnerClosure(
      problem, complementPartners, symbols, supportCache);
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

std::vector<size_t> sortCurrentFrameSymbolSeed(
    std::unordered_set<size_t> symbols) {
  return sortUniqueSymbols(std::move(symbols));
} // LCOV_EXCL_LINE

const std::vector<size_t>& cachedClosedCurrentFrameSymbols(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    std::vector<size_t> seedSymbols,
    PdrFormulaSupportCache* supportCache) {
  const auto existing = cache.closedCurrentFrameSymbols.find(seedSymbols);
  if (existing != cache.closedCurrentFrameSymbols.end()) {
    return existing->second; // LCOV_EXCL_LINE
  }
  if (cache.closedCurrentFrameSymbols.size() >=
      kMaxPredecessorClosedSymbolCacheEntries) {
    // The cache is an accelerator for repeated local cones only. Clearing it is
    // cheaper and more predictable than retaining thousands of one-off
    // projected predecessor surfaces in a long SEC run.
    cache.closedCurrentFrameSymbols.clear(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE

  std::unordered_set<size_t> symbols(seedSymbols.begin(), seedSymbols.end());
  std::vector<size_t> closedSymbols = sortClosedCurrentFrameSymbols(
      problem, complementPartners, std::move(symbols), supportCache);
  auto [inserted, insertedNew] = cache.closedCurrentFrameSymbols.emplace(
      std::move(seedSymbols), std::move(closedSymbols));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor closed symbol cache seed=",
        inserted->first.size(),
        " closed=",
        inserted->second.size(),
        " entries=",
        cache.closedCurrentFrameSymbols.size());
  }
  return inserted->second;
}

PredecessorFrameSymbolSurfaceKey makePredecessorFrameSymbolSurfaceKey(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    PdrFormulaSupportCache* supportCache) {
  PredecessorFrameSymbolSurfaceKey key;
  key.problem = &problem;
  key.initFormula = initFormula;
  key.frameInvariant = frameInvariant;
  key.complementPartners = &complementPartners;
  key.supportCache = supportCache;
  key.level = level;
  key.frameFingerprint = frameClausesFingerprint(frames, level);
  key.exactFrameClauses = exactFrameClauses;
  return key;
}

std::vector<size_t> buildStablePredecessorCurrentFrameSymbols(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    PdrFormulaSupportCache* supportCache) {
  std::unordered_set<size_t> symbols;
  if (level == 0) {
    if (!hasStructuredInitFacts(problem)) {
      addFormulaSymbols(initFormula, symbols, supportCache);
    }
    if (problem.resetBootstrapCycles != 0 && problem.property != nullptr) {
      addFormulaSymbols(problem.property, symbols, supportCache); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    addAllFrameClauseSymbols(frames[0], symbols);
  } else {
    addFormulaSymbols(frameInvariant, symbols, supportCache); // LCOV_EXCL_LINE
    addAllFrameClauseSymbols(frames[level], symbols); // LCOV_EXCL_LINE
  }

  // The relation closures below are independent of the target cube. Closing
  // this stable frame side once is equivalent to closing it together with each
  // query's dynamic symbols, because the closures only add partner/equality
  // symbols and do not inspect SAT polarity or clause state.
  return sortClosedCurrentFrameSymbols(
      problem, complementPartners, std::move(symbols), supportCache);
}

const std::vector<size_t>& cachedStablePredecessorCurrentFrameSymbols(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    PdrFormulaSupportCache* supportCache) {
  const PredecessorFrameSymbolSurfaceKey key =
      makePredecessorFrameSymbolSurfaceKey(
          problem,
          initFormula,
          frameInvariant,
          frames,
          level,
          complementPartners,
          exactFrameClauses,
          supportCache);
  if (!cache.currentFrameSymbols.valid ||
      !(cache.currentFrameSymbols.key == key)) { // LCOV_EXCL_LINE
    cache.currentFrameSymbols.symbols =
        buildStablePredecessorCurrentFrameSymbols(
            problem,
            initFormula,
            frameInvariant,
            frames,
            level,
            complementPartners,
            supportCache);
    cache.currentFrameSymbols.key = key;
    cache.currentFrameSymbols.valid = true;
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor frame symbol cache built level=",
          level,
          " symbols=",
          cache.currentFrameSymbols.symbols.size(),
          " frame_fingerprint=",
          key.frameFingerprint);
    }
  }
  return cache.currentFrameSymbols.symbols;
}

std::vector<size_t> mergePredecessorSymbolAddition(
    std::vector<size_t> base,
    const std::vector<size_t>& addition) {
  if (addition.empty()) {
    return base;
  }
  return detail::mergeSortedPdrSymbolVectors(base, addition);
}

std::vector<size_t> predecessorCurrentFrameQuerySymbolsFromCachedSurface(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    const std::vector<size_t>& predecessorSymbols,
    const std::vector<size_t>& transitionSupportSymbols,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    const std::vector<StateClause>* extraFrameClauses,
    PredecessorAssumptionCache& predecessorAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  const std::vector<size_t>& stableSymbols =
      cachedStablePredecessorCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          initFormula,
          frameInvariant,
          frames,
          level,
          complementPartners,
          exactFrameClauses,
          supportCache);
  std::vector<size_t> merged = stableSymbols;

  std::unordered_set<size_t> predecessorDynamic;
  predecessorDynamic.reserve(predecessorSymbols.size());
  predecessorDynamic.insert(predecessorSymbols.begin(), predecessorSymbols.end());
  if (level == 0 && hasStructuredInitFacts(problem)) {
    // Structured Init facts are intentionally query-local. Apply them only to
    // the predecessor cone, matching addFrameConstraintSymbols() before the
    // cached stable frame side is merged in.
    addRelevantInitConstraintSymbols(problem, predecessorDynamic); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  merged = mergePredecessorSymbolAddition(
      std::move(merged),
      cachedClosedCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(predecessorDynamic)),
          supportCache));

  std::unordered_set<size_t> transitionDynamic;
  transitionDynamic.reserve(transitionSupportSymbols.size());
  if (predecessorSourceFrameIsKnownSafe(level)) {
    addFormulaSymbols(problem.property, transitionDynamic, supportCache); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      transitionDynamic.insert(symbol);
    }
  }
  merged = mergePredecessorSymbolAddition(
      std::move(merged),
      cachedClosedCurrentFrameSymbols(
          predecessorAssumptionCache,
          problem,
          complementPartners,
          sortCurrentFrameSymbolSeed(std::move(transitionDynamic)),
          supportCache));

  std::unordered_set<size_t> tailSymbols;
  tailSymbols.reserve(
      (excludeTargetOnCurrentFrame ? targetCube.size() : 0) +
      (extraFrameClauses == nullptr ? 0 : extraFrameClauses->size()));
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, tailSymbols); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) { // LCOV_EXCL_LINE
      addClauseSymbols(clause, tailSymbols); // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE
  return mergePredecessorSymbolAddition(
      std::move(merged), sortUniqueSymbols(std::move(tailSymbols)));
}

std::vector<size_t> predecessorCurrentFrameQuerySymbols(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    const std::vector<size_t>& predecessorSymbols,
    const std::vector<size_t>& transitionSupportSymbols,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    const std::vector<StateClause>* extraFrameClauses,
    PredecessorAssumptionCache* predecessorAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  if (predecessorAssumptionCache != nullptr &&
      hasLocalDualRailFinalLeafRepairSurface(problem) &&
      exactFrameClauses) {
    return predecessorCurrentFrameQuerySymbolsFromCachedSurface(
        problem,
        initFormula,
        frameInvariant,
        frames,
        level,
        targetCube,
        excludeTargetOnCurrentFrame,
        predecessorSymbols,
        transitionSupportSymbols,
        complementPartners,
        exactFrameClauses,
        extraFrameClauses,
        *predecessorAssumptionCache,
        supportCache);
  }

  std::unordered_set<size_t> symbols;
  symbols.reserve(
      predecessorSymbols.size() + transitionSupportSymbols.size() +
      (excludeTargetOnCurrentFrame ? targetCube.size() : 0));
  symbols.insert(predecessorSymbols.begin(), predecessorSymbols.end());
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      exactFrameClauses,
      complementPartners,
      symbols,
      supportCache);
  if (predecessorSourceFrameIsKnownSafe(level)) {
    // The safe-frame property is encoded below, but it must not widen the
    // projected learned-frame surface. Otherwise every property-support state
    // bit can pull in large neighborhoods of unrelated frame clauses.
    addFormulaSymbols(problem.property, symbols, supportCache);
  }
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(supportCache, problem.dualRailStatePairs, symbols);
  if (excludeTargetOnCurrentFrame) {
    addCubeSymbols(targetCube, symbols);
  }
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) {
      addClauseSymbols(clause, symbols);
    }
  }
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> predecessorAssumptionCacheSymbols(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& solverSymbols,
    bool exactFrameClauses,
    size_t level,
    PredecessorAssumptionCache* cache) {
  if (!detail::shouldUseStableLocalPredecessorCacheSurface(
          hasLocalDualRailFinalLeafRepairSurface(problem),
          exactFrameClauses,
          level)) {
    return solverSymbols;
  }

  // Local single-output dual-rail leaves issue many neighboring predecessor
  // queries. A stable local surface lets the cached SAT solver survive small
  // target/support changes without promoting the query to all dual-rail state
  // symbols; sampled Swerv leaves spent the wall on those broad level-0 caches.
  if (cache != nullptr) {
    if (cache->widenedPredecessorCacheResolver != &transitionByState) {
      cache->widenedPredecessorCacheSymbols.clear();
      cache->widenedPredecessorCacheResolver = &transitionByState;
    }
    if (detail::widenSortedPdrSymbolSurface(
            cache->widenedPredecessorCacheSymbols, solverSymbols)) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor cached solver surface widened symbols=",
            cache->widenedPredecessorCacheSymbols.size(),
            " requested=",
            solverSymbols.size());
      }
    }
    return cache->widenedPredecessorCacheSymbols;
  }

  return solverSymbols; // LCOV_EXCL_LINE
}

std::vector<size_t> initIntersectionSymbols(const KInductionProblem& problem,
                                            BoolExpr* initFormula,
                                            const StateCube& cube) {
  // Init-intersection checks are issued many times during cube
  // generalization. They only need the startup formula, the candidate cube, and
  // complemented partners of those bits; allocating every SEC state/input here
  // made PDR spend most of its time constructing throwaway SAT variables.
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(initFormula, symbols);
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  addRelevantComplementedStatePartners(problem.complementedStatePairs0, symbols);
  addRelevantComplementedStatePartners(problem.complementedStatePairs1, symbols);
  addRelevantSameFrameStateEqualityPartners(problem, symbols);
  addRelevantDualRailPartners(problem.dualRailStatePairs, symbols);
  return sortUniqueSymbols(std::move(symbols));
}

std::optional<bool> findCubeLiteralValue(const StateCube& cube, size_t symbol) {
  const auto it = std::lower_bound(
      cube.begin(),
      cube.end(),
      symbol,
      [](const CubeLiteral& literal, size_t requestedSymbol) {
        return literal.symbol < requestedSymbol;
      // LCOV_EXCL_START
      });
      // LCOV_EXCL_STOP
  if (it == cube.end() || it->symbol != symbol) {
    return std::nullopt;
  }
  return it->value;
}

bool contradictsAssignments(
    const StateCube& cube,
    const std::vector<std::pair<size_t, bool>>& initAssignments) {
  for (const auto& [symbol, value] : initAssignments) {
    if (const auto cubeValue = findCubeLiteralValue(cube, symbol);
        cubeValue.has_value() && *cubeValue != value) {
      // LCOV_EXCL_START
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  return false;
}

bool contradictsEqualities(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& equalities) {
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsValue = findCubeLiteralValue(cube, lhsSymbol);
    // LCOV_EXCL_START
    const auto rhsValue = findCubeLiteralValue(cube, rhsSymbol);
    if (lhsValue.has_value() && rhsValue.has_value() &&
        *lhsValue != *rhsValue) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  return false;
}

bool contradictsComplements(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& complements) {
  for (const auto& [primarySymbol, complementedSymbol] : complements) {
    const auto primaryValue = findCubeLiteralValue(cube, primarySymbol);  // LCOV_EXCL_LINE
    const auto complementedValue = findCubeLiteralValue(cube, complementedSymbol);  // LCOV_EXCL_LINE
    if (primaryValue.has_value() && complementedValue.has_value() &&  // LCOV_EXCL_LINE
        *primaryValue == *complementedValue) {  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
  }
  return false;
}

void reservePdrTransitionEncodingVars(SATSolverWrapper& solver,
                                      size_t estimatedNodes) {
  if (estimatedNodes < kMinPdrTransitionSolverReserveNodes) {
    return;
  }
  solver.reserveAdditionalVars( // LCOV_EXCL_LINE
      std::min(estimatedNodes, kMaxPdrTransitionSolverReserveHint)); // LCOV_EXCL_LINE
}

const std::vector<std::pair<size_t, size_t>>& emptySymbolPairs() {
  static const std::vector<std::pair<size_t, size_t>> pairs;
  return pairs;
}

// LCOV_EXCL_START
std::optional<bool> cubeIntersectsKnownInitFacts(
// LCOV_EXCL_STOP
    const KInductionProblem& problem,
    const StateCube& cube) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                // LCOV_EXCL_START
                                ? problem.bootstrapStateAssignments
                                // LCOV_EXCL_STOP
                                : problem.initialStateAssignments;
  const auto& equalities =
      KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()
          ? (usesBootstrapFrontier ? problem.bootstrapStateEqualityPairs
                                   : problem.initialStateEqualityPairs) // LCOV_EXCL_LINE
          : emptySymbolPairs();

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  if (contradictsAssignments(cube, assignments) ||
      contradictsEqualities(cube, equalities)) {
    return false;  // LCOV_EXCL_LINE
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs0)) {
    return false;  // LCOV_EXCL_LINE
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs1)) {
    return false;  // LCOV_EXCL_LINE
  }

  // The structured init/bootstrap facts are a cheap, explicit abstraction of
  // the startup frontier. If they do not visibly exclude this cube, be
  // conservative and keep the cube as init-intersecting instead of spending a
  // large SAT query only to drop one more literal during generalization.
  if (usesBootstrapFrontier || !assignments.empty() || !equalities.empty()) {
    return true;
  }
  return std::nullopt;
}

void addTransitionRelationForTargets(
    SATSolverWrapper& solver,
    // LCOV_EXCL_START
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    bool createMissingTransitionLeaves = false,
    // LCOV_EXCL_STOP
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  for (const auto& group :
       groupTransitionTargetsBySymbolMap(transitionByState, encodedTargets)) {
    std::unordered_map<size_t, int> leafLits =
        variables.makeLeafLits(frame, supportSymbols);
    const size_t estimatedNodes =
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols);
    reservePdrTransitionEncodingVars(solver, estimatedNodes);
    FrameFormulaEncoder encoder(
        solver,
        std::move(leafLits),
        group.symbolMap,
        createMissingTransitionLeaves,
        // LCOV_EXCL_START
        estimatedNodes);
    for (const auto stateSymbol : group.stateSymbols) {
      const TransitionExprView view =
          transitionByState.expressionView(stateSymbol);
      if (view.symbolMap != group.symbolMap) {
      // LCOV_EXCL_STOP
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      addLiteralEquivalence(
          solver,
          variables.getLiteral(stateSymbol, frame + 1),
          // LCOV_EXCL_STOP
          encoder.encode(view.expr));
    }
    if (encodedLeafLits != nullptr) {
      const auto& groupLeafLits = encoder.leafLits();  // LCOV_EXCL_LINE
      encodedLeafLits->insert(groupLeafLits.begin(), groupLeafLits.end());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
}

void addTransitionConstraintsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  (void)encodedTargets;
  // LCOV_EXCL_STOP
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    std::unordered_map<size_t, int> leafLits =
        variables.makeLeafLits(frame, supportSymbols);
    const size_t estimatedNodes =
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols);
    reservePdrTransitionEncodingVars(solver, estimatedNodes);
    FrameFormulaEncoder encoder(
        solver,
        std::move(leafLits),
        // LCOV_EXCL_START
        group.symbolMap,
        false,
        estimatedNodes);
    for (const auto& literal : group.literals) {
      const TransitionExprView view =
      // LCOV_EXCL_STOP
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder.encode(view.expr);
      solver.addClause({literal.desiredValue ? transitionLit : -transitionLit});
    }
    if (encodedLeafLits != nullptr) {
      const auto& groupLeafLits = encoder.leafLits();
      encodedLeafLits->insert(groupLeafLits.begin(), groupLeafLits.end());
    }
  }
}

std::vector<std::pair<int, CubeLiteral>> addTransitionAssumptionsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_START
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  (void)encodedTargets;
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  // LCOV_EXCL_STOP
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    std::unordered_map<size_t, int> leafLits =
        variables.makeLeafLits(frame, supportSymbols);
    const size_t estimatedNodes =
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols);
    reservePdrTransitionEncodingVars(solver, estimatedNodes);
    FrameFormulaEncoder encoder(
        solver,
        std::move(leafLits),
        // LCOV_EXCL_START
        group.symbolMap,
        false,
        estimatedNodes);
    for (const auto& literal : group.literals) {
      const TransitionExprView view =
      // LCOV_EXCL_STOP
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder.encode(view.expr);
      assumptions.emplace_back(
          literal.desiredValue ? transitionLit : -transitionLit,
          literal.originalLiteral);
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
  return assumptions;
}

FrameFormulaEncoder& cachedPredecessorTransitionEncoder(
    PredecessorAssumptionSolver& cachedSolver,
    const std::unordered_map<size_t, size_t>* symbolMap,
    size_t frame,
    size_t estimatedNodes) {
  const auto existing =
      cachedSolver.transitionEncoderBySymbolMap.find(symbolMap);
  if (existing != cachedSolver.transitionEncoderBySymbolMap.end()) {
    return *existing->second;
  }

  // Use the cached solver's complete symbol surface for this encoder. It is
  // built once per reusable predecessor solver, and it prevents a later target
  // in the same surface from missing a leaf that was outside the first target's
  // transition support slice.
  auto encoder = std::make_unique<FrameFormulaEncoder>(
      *cachedSolver.solver,
      cachedSolver.variables->makeLeafLits(frame),
      symbolMap,
      false,
      estimatedNodes);
  cachedSolver.transitionLeafLits.insert(
      encoder->leafLits().begin(), encoder->leafLits().end());
  auto [inserted, insertedNew] =
      cachedSolver.transitionEncoderBySymbolMap.emplace(
          symbolMap, std::move(encoder));
  (void)insertedNew;
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor transition encoder cached symbols=",
        inserted->second->leafLits().size(),
        " estimated_nodes=",
        estimatedNodes);
  }
  return *inserted->second;
}

std::vector<std::pair<int, CubeLiteral>>
addCachedTransitionAssumptionsForTargetCube(
    PredecessorAssumptionSolver& cachedSolver,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  (void)encodedTargets;
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    FrameFormulaEncoder* encoder = nullptr;
    for (const auto& literal : group.literals) {
      const TransitionAssumptionKey key{
          literal.transitionSymbol,
          literal.desiredValue};
      const auto cachedIt =
          cachedSolver.assumptionByTransitionLiteral.find(key);
      if (cachedIt != cachedSolver.assumptionByTransitionLiteral.end()) {
        assumptions.emplace_back(cachedIt->second, literal.originalLiteral);
        continue;
      }

      if (encoder == nullptr) {
        const size_t estimatedNodes =
            estimateTransitionEncodingNodes(
                transitionByState, group.stateSymbols);
        reservePdrTransitionEncodingVars(*cachedSolver.solver, estimatedNodes);
        encoder = &cachedPredecessorTransitionEncoder(
            cachedSolver,
            group.symbolMap,
            frame,
            estimatedNodes);
      }
      const TransitionExprView view =
          transitionByState.expressionView(literal.transitionSymbol);
      if (view.symbolMap != group.symbolMap) {
        throw std::runtime_error("Inconsistent transition symbol map");  // LCOV_EXCL_LINE
      }
      const int transitionLit = encoder->encode(view.expr);
      // Store both polarities once the transition root is encoded. Neighboring
      // PDR cubes often ask for the opposite value of the same next-state bit;
      // reusing the root literal avoids rebuilding the same transition cone.
      cachedSolver.assumptionByTransitionLiteral.emplace(
          TransitionAssumptionKey{literal.transitionSymbol, true},
          transitionLit);
      cachedSolver.assumptionByTransitionLiteral.emplace(
          TransitionAssumptionKey{literal.transitionSymbol, false},
          -transitionLit);
      const int assumptionLit =
          literal.desiredValue ? transitionLit : -transitionLit;
      assumptions.emplace_back(assumptionLit, literal.originalLiteral);
    }
  }
  return assumptions;
}

std::vector<int> assumptionLiteralsFromPairs(
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    (void)cubeLiteral;
    assumptions.push_back(assumptionLit);
  }
  return assumptions;
}

std::unordered_map<int, CubeLiteral> literalByAssumptionFromTargetPairs(
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // Keep the polarity-tolerant mapping used by the fresh core oracle. Some
    // solver backends expose final conflicts in solver-literal polarity.
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }
  return literalByAssumption;
}

StateCube failedAssumptionCubeFromTargetPairs(
    const SATSolverWrapper& solver,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  const auto literalByAssumption =
      literalByAssumptionFromTargetPairs(assumptionPairs);

  StateCube core;
  for (const int failedLit : solver.failedAssumptions()) {
    const auto literalIt = literalByAssumption.find(failedLit);
    if (literalIt == literalByAssumption.end()) {
      continue;
    }
    core.push_back(literalIt->second);
  }
  normalizeCube(core);
  return core;
}

std::optional<StateCube> minimizeCoreInTargetContext(
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks);

bool shouldMinimizeCachedPredecessorCoreInTargetContext(
    const KInductionProblem& problem,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& transitionSupportSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    const StateCube& currentCore) {
  if (!problem.usesDualRailStateEncoding || level != 0 ||
      excludeTargetOnCurrentFrame || extraFrameClauses != nullptr) {
    return false;
  }
  if (targetCube.size() < kMinMediumCubePredecessorCoreTargetSize ||
      transitionSupportSymbols.size() <=
          kMaxGeneralizedBlockedCubeTransitionSupport) {
    return false;
  }
  return currentCore.empty() || currentCore.size() >= targetCube.size();
}

StateCube cachedPredecessorUnsatCoreFromTargetContext(
    SATSolverWrapper& solver,
    const KInductionProblem& problem,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& transitionSupportSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    const std::vector<int>& targetAssumptions,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  StateCube core =
      failedAssumptionCubeFromTargetPairs(solver, assumptionPairs);
  if (!shouldMinimizeCachedPredecessorCoreInTargetContext(
          problem,
          level,
          targetCube,
          transitionSupportSymbols,
          excludeTargetOnCurrentFrame,
          extraFrameClauses,
          core)) {
    return core;
  }

  // The cached predecessor solver already contains the exact F0/frame and
  // transition context that proved the full target unreachable. Shrink only
  // the target assumptions inside that same solver, and accept a reduced core
  // only when it remains UNSAT there.
  size_t checks = 0; // LCOV_EXCL_LINE
  const auto literalByAssumption =
      literalByAssumptionFromTargetPairs(assumptionPairs); // LCOV_EXCL_LINE
  const auto minimizedCore = minimizeCoreInTargetContext( // LCOV_EXCL_LINE
      solver, targetAssumptions, literalByAssumption, &checks); // LCOV_EXCL_LINE
  if (!minimizedCore.has_value() || // LCOV_EXCL_LINE
      minimizedCore->size() >= targetCube.size()) { // LCOV_EXCL_LINE
    if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
      emitSecDiag( // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor cached core minimization miss target=",
          targetCube.size(), // LCOV_EXCL_LINE
          " raw_core=",
          core.size(), // LCOV_EXCL_LINE
          " checks=",
          checks,
          " level=",
          level,
          " support=",
          transitionSupportSymbols.size()); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    return core; // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor cached core minimized target=",
        targetCube.size(), // LCOV_EXCL_LINE
        "->",
        minimizedCore->size(), // LCOV_EXCL_LINE
        " raw_core=",
        core.size(), // LCOV_EXCL_LINE
        " checks=",
        checks,
        " level=",
        level,
        " support=",
        transitionSupportSymbols.size(), // LCOV_EXCL_LINE
        " target_hash=",
        cubeFingerprint(targetCube), // LCOV_EXCL_LINE
        " core_hash=",
        cubeFingerprint(*minimizedCore)); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return *minimizedCore; // LCOV_EXCL_LINE
}

int cachedTargetExclusionAssumption(
    PredecessorAssumptionSolver& cachedSolver,
    const StateCube& targetCube,
    size_t frame) {
  const StateClause exclusionClause = clauseFromCube(targetCube);
  const auto cachedIt =
      cachedSolver.exclusionAssumptionByClause.find(exclusionClause);
  if (cachedIt != cachedSolver.exclusionAssumptionByClause.end()) {
    return cachedIt->second; // LCOV_EXCL_LINE
  }

  const int selector = cachedSolver.solver->newVar();
  std::vector<int> satClause;
  satClause.reserve(exclusionClause.size() + 1);
  satClause.push_back(-selector);
  for (const auto& literal : exclusionClause) {
    if (!cachedSolver.variables->hasSymbol(literal.symbol)) {
      throw std::runtime_error( // LCOV_EXCL_LINE
          "PDR cached negated-cube encoding missing symbol " + // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " + // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " + // LCOV_EXCL_LINE
          std::to_string(targetCube.size())); // LCOV_EXCL_LINE
    }
    const int satLiteral =
        cachedSolver.variables->getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  cachedSolver.solver->addClause(satClause);
  cachedSolver.exclusionAssumptionByClause.emplace(exclusionClause, selector);
  return selector;
}

int cachedExtraFrameClauseAssumption( // LCOV_EXCL_LINE
    PredecessorAssumptionSolver& cachedSolver,
    const StateClause& clause,
    size_t frame) {
  const auto cachedIt =
      cachedSolver.extraFrameAssumptionByClause.find(clause); // LCOV_EXCL_LINE
  if (cachedIt != cachedSolver.extraFrameAssumptionByClause.end()) { // LCOV_EXCL_LINE
    return cachedIt->second; // LCOV_EXCL_LINE
  }

  const int selector = cachedSolver.solver->newVar(); // LCOV_EXCL_LINE
  std::vector<int> satClause; // LCOV_EXCL_LINE
  satClause.reserve(clause.size() + 1); // LCOV_EXCL_LINE
  satClause.push_back(-selector); // LCOV_EXCL_LINE
  for (const auto& literal : clause) { // LCOV_EXCL_LINE
    if (!cachedSolver.variables->hasSymbol(literal.symbol)) { // LCOV_EXCL_LINE
      throw std::runtime_error( // LCOV_EXCL_LINE
          "PDR cached extra-frame clause missing symbol " + // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " + // LCOV_EXCL_LINE
          std::to_string(frame) + " in clause of size " + // LCOV_EXCL_LINE
          std::to_string(clause.size())); // LCOV_EXCL_LINE
    }
    const int satLiteral = // LCOV_EXCL_LINE
        cachedSolver.variables->getLiteral(literal.symbol, frame); // LCOV_EXCL_LINE
    satClause.push_back(literal.positive ? satLiteral : -satLiteral); // LCOV_EXCL_LINE
  }
  cachedSolver.solver->addClause(satClause); // LCOV_EXCL_LINE
  cachedSolver.extraFrameAssumptionByClause.emplace(clause, selector); // LCOV_EXCL_LINE
  return selector; // LCOV_EXCL_LINE
} // LCOV_EXCL_LINE

std::optional<StateCube> findPreviousResetCoreImpliedByOneStepTransition(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    // LCOV_EXCL_START
    const TransitionExprResolver& transitionByState,
    // LCOV_EXCL_STOP
    const StateCube& targetCube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache) {
  if (postBootstrapSteps == 0) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_START
  const auto previousIt =
  // LCOV_EXCL_STOP
      cache.resetUnreachableCoresByPostBootstrapStep.find(
          postBootstrapSteps - 1);
  if (previousIt ==
          cache.resetUnreachableCoresByPostBootstrapStep.end() ||
      previousIt->second.empty()) {
    // LCOV_EXCL_START
    return std::nullopt;
  }
  // LCOV_EXCL_STOP

  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  // LCOV_EXCL_START
  if (encodedTargets.empty()) {
  // LCOV_EXCL_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
      // LCOV_EXCL_STOP
  if (transitionSupportSymbols.size() >
      kMaxPreviousResetCoreImplicationSupport) {
    if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: previous reset blocker implication skipped "
          "reason=support_cap post_bootstrap_steps=",
          postBootstrapSteps,
          // LCOV_EXCL_START
          " support=",
          // LCOV_EXCL_STOP
          transitionSupportSymbols.size(),  // LCOV_EXCL_LINE
          " target_cube=",
          // LCOV_EXCL_START
          targetCube.size());  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  size_t checks = 0;
  for (const StateCube& previousCore : previousIt->second) {
    if (previousCore.empty() ||
        previousCore.size() >
            kMaxPreviousResetCoreImplicationCoreLiterals) {
      continue;  // LCOV_EXCL_LINE
    }
    if (++checks > kMaxPreviousResetCoreImplicationChecks) {
      break;  // LCOV_EXCL_LINE
    }

    std::unordered_set<size_t> querySymbols(
        // LCOV_EXCL_START
        transitionSupportSymbols.begin(), transitionSupportSymbols.end());
        // LCOV_EXCL_STOP
    for (const auto& literal : previousCore) {
      querySymbols.insert(literal.symbol);
    }
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs0, querySymbols);
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs1, querySymbols);
    addRelevantSameFrameStateEqualityPartners(problem, querySymbols);
    addRelevantDualRailPartners(problem.dualRailStatePairs, querySymbols);
    const std::vector<size_t> solverSymbols =
        sortUniqueSymbols(std::move(querySymbols));
    if (solverSymbols.size() >
        kMaxPreviousResetCoreImplicationSupport) {
      continue;  // LCOV_EXCL_LINE
    }

    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(solverSymbols.size());
    FrameVariableStore variables(solver, solverSymbols, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs0, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs1, 1);
    addSameFrameStateEqualities(solver, variables, problem, 1);
    addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
    addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
    addTransitionConstraintsForTargetCube(
        solver,
        // LCOV_EXCL_START
        variables,
        // LCOV_EXCL_STOP
        transitionByState,
        0,
        // LCOV_EXCL_START
        targetCube,
        encodedTargets,
        // LCOV_EXCL_STOP
        transitionSupportSymbols);
    addNegatedCubeClause(solver, variables, previousCore, 0);

    SATSolverWrapper::SolveStatus status = SATSolverWrapper::SolveStatus::Sat;
    // LCOV_EXCL_START
    if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
    // LCOV_EXCL_STOP
      status = solver.solveWithKissatResourceLimits(
          // LCOV_EXCL_START
          kPreviousResetCoreImplicationConflictLimit);
          // LCOV_EXCL_STOP
    } else {
      // LCOV_EXCL_START
      status = solver.solveStatus();  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    // LCOV_EXCL_START
    if (status == SATSolverWrapper::SolveStatus::Unsat) {
      if (pdrStatsEnabled() || pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
            "SEC PDR stats: previous reset blocker implication ",
            "post_bootstrap_steps=",
            // LCOV_EXCL_START
            postBootstrapSteps,
            " target_cube=",
            // LCOV_EXCL_STOP
            targetCube.size(),  // LCOV_EXCL_LINE
            " previous_core=",
            previousCore.size(),  // LCOV_EXCL_LINE
            " support=",
            // LCOV_EXCL_START
            transitionSupportSymbols.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            " solver_symbols=",
            // LCOV_EXCL_START
            solverSymbols.size());  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return previousCore;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
    if (status == SATSolverWrapper::SolveStatus::Unknown &&
        pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: previous reset blocker implication skipped "
          "reason=solver_resource_limit post_bootstrap_steps=",
          postBootstrapSteps,
          " target_cube=",
          targetCube.size(),  // LCOV_EXCL_LINE
          " previous_core=",
          previousCore.size(),  // LCOV_EXCL_LINE
          " solver_symbols=",
          // LCOV_EXCL_START
          solverSymbols.size());  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
  }
  return std::nullopt;
}

// LCOV_EXCL_START


// LCOV_EXCL_STOP
std::optional<StateCube> proveTransitionImpossibleResetCoreForCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    ResetFrontierCache& cache) {
  if (problem.resetBootstrapCycles == 0) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (const auto cachedCore =
          // LCOV_EXCL_START
          findTransitionImpossibleResetCoreForCube(cache, cube);
          // LCOV_EXCL_STOP
      cachedCore.has_value()) {
    return cachedCore;  // LCOV_EXCL_LINE
  }

  std::vector<StateCube> candidates;
  std::vector<StateCube> cachedCores;
  // LCOV_EXCL_START
  std::unordered_set<StateCube, StateCubeHash> candidateKeys;
  // LCOV_EXCL_STOP
  for (const auto& [_, cores] : cache.resetUnreachableCoresByPostBootstrapStep) {
    (void)_;
    for (const StateCube& core : cores) {
      if (core.empty() ||
          core.size() > kMaxTransitionImpossibleResetCoreLiterals ||
          !cubeContainsCube(cube, core)) {
        continue;  // LCOV_EXCL_LINE
      }
      const StateCube key = resetFrontierCacheKey(core, 0).cube;
      const auto memoIt = cache.transitionImpossibleResetCoreByKey.find(key);
      if (memoIt != cache.transitionImpossibleResetCoreByKey.end()) {
        if (memoIt->second) {
          cachedCores.push_back(core);  // LCOV_EXCL_LINE
        } // LCOV_EXCL_LINE
        continue;
      // LCOV_EXCL_START
      }
      if (candidateKeys.insert(key).second) {
        candidates.push_back(core);
        // LCOV_EXCL_STOP
      }
    // LCOV_EXCL_START
    }
  }
  // LCOV_EXCL_STOP
  if (!cachedCores.empty()) {
    sortStateCubesDeterministically(cachedCores); // LCOV_EXCL_LINE
    return cachedCores.front();  // LCOV_EXCL_LINE
  }
  if (candidates.empty()) {
    return std::nullopt;
  }

  sortStateCubesDeterministically(candidates);

  // LCOV_EXCL_START
  for (const StateCube& candidate : candidates) {
    const StateCube key = resetFrontierCacheKey(candidate, 0).cube;
    const std::vector<size_t> targetSymbols = cubeStateSymbols(candidate);
    // LCOV_EXCL_STOP
    const std::vector<size_t> encodedTargets =
        expandTransitionTargets(problem, targetSymbols, transitionByState);
    // LCOV_EXCL_START
    if (encodedTargets.empty()) {
    // LCOV_EXCL_STOP
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
    }
    const std::vector<size_t> transitionSupportSymbols =
    // LCOV_EXCL_STOP
        collectTransitionSupportSymbols(transitionByState, encodedTargets);
    if (transitionSupportSymbols.size() >
        kMaxTransitionImpossibleResetCoreSupport) {
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);  // LCOV_EXCL_LINE
      if (pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: transition-impossible reset core skipped "
            "reason=support_cap core=",
            candidate.size(),  // LCOV_EXCL_LINE
            " support=",
            transitionSupportSymbols.size());  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP

    std::unordered_set<size_t> querySymbols(
        transitionSupportSymbols.begin(), transitionSupportSymbols.end());
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs0, querySymbols);
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs1, querySymbols);
    addRelevantSameFrameStateEqualityPartners(problem, querySymbols);
    addRelevantDualRailPartners(problem.dualRailStatePairs, querySymbols);
    const std::vector<size_t> solverSymbols =
        sortUniqueSymbols(std::move(querySymbols));
    if (solverSymbols.size() > kMaxTransitionImpossibleResetCoreSupport) {
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }

    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(solverSymbols.size());
    FrameVariableStore variables(solver, solverSymbols, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs0, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs1, 1);
    addSameFrameStateEqualities(solver, variables, problem, 1);
    addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
    addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
    addTransitionConstraintsForTargetCube(
        // LCOV_EXCL_START
        solver,
        // LCOV_EXCL_STOP
        variables,
        transitionByState,
        // LCOV_EXCL_START
        0,
        candidate,
        encodedTargets,
        // LCOV_EXCL_STOP
        transitionSupportSymbols);

// LCOV_EXCL_START

    SATSolverWrapper::SolveStatus status = SATSolverWrapper::SolveStatus::Sat;
    if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      status = solver.solveWithKissatResourceLimits(
          kTransitionImpossibleResetCoreConflictLimit);
    } else {
      status = solver.solveStatus();  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    if (status == SATSolverWrapper::SolveStatus::Unsat) {
      rememberTransitionImpossibleResetCore(cache, candidate);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      if (pdrStatsEnabled() || pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
            "SEC PDR stats: transition-impossible reset core ",
            "cube=", cube.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            " core=", candidate.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            " support=", transitionSupportSymbols.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            " solver_symbols=", solverSymbols.size(),  // LCOV_EXCL_LINE
            " hash=", cubeFingerprint(candidate));  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
    cache.transitionImpossibleResetCoreByKey.emplace(key, false);
    if (status == SATSolverWrapper::SolveStatus::Unknown &&
        pdrResetShortcutDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: transition-impossible reset core skipped "
          "reason=solver_resource_limit core=",
          candidate.size(),  // LCOV_EXCL_LINE
          " solver_symbols=",
          solverSymbols.size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_START
  return std::nullopt;
  // LCOV_EXCL_STOP
}

std::optional<StateCube> resetSpecializedPriorCoreConflictAtStep(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    // LCOV_EXCL_START
    size_t targetStep,
    // LCOV_EXCL_STOP
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant,
    bool allowDeepSmallCubeRelaxedBudget = true) {
  // LCOV_EXCL_START
  if (postBootstrapSteps == 0) {
  // LCOV_EXCL_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  }

// LCOV_EXCL_START

  struct PriorResetCoreCandidate {
    StateCube core;
    size_t knownStep = 0;
  };
  std::vector<PriorResetCoreCandidate> candidates;
  std::unordered_map<StateCube, size_t, StateCubeHash> candidateIndexByKey;
  // LCOV_EXCL_STOP
  for (const auto& [knownStep, cores] :
       cache.resetUnreachableCoresByPostBootstrapStep) {
    if (knownStep >= postBootstrapSteps) {
      continue;  // LCOV_EXCL_LINE
    }
    for (const StateCube& core : cores) {
      // LCOV_EXCL_START
      if (core.empty() || core.size() >= cube.size() ||
          !cubeContainsCube(cube, core)) {
        continue;
      }
      StateCube key = resetFrontierCacheKey(core, 0).cube;
      if (const auto it = candidateIndexByKey.find(key);
          it != candidateIndexByKey.end()) {
        candidates[it->second].knownStep =
            std::max(candidates[it->second].knownStep, knownStep);
      } else {
        candidateIndexByKey.emplace(key, candidates.size());
        candidates.push_back({std::move(key), knownStep});
      }
    // LCOV_DISABLED_START
    }
  }
  // LCOV_DISABLED_STOP
  if (candidates.empty()) {
    // LCOV_DISABLED_START
    return std::nullopt;
  }

  std::sort(
      candidates.begin(),
      candidates.end(),
      [](const PriorResetCoreCandidate& lhs,
         const PriorResetCoreCandidate& rhs) {
        if (lhs.knownStep != rhs.knownStep) {
          return lhs.knownStep > rhs.knownStep;
        }
        if (lhs.core.size() != rhs.core.size()) {
          return lhs.core.size() < rhs.core.size();
        }
        return std::lexicographical_compare(
            lhs.core.begin(),
            lhs.core.end(),
            rhs.core.begin(),
            rhs.core.end(),
            cubeLiteralLess);
      });  // LCOV_EXCL_LINE

  size_t probes = 0;
  for (const auto& candidate : candidates) {
    if (probes++ >= kMaxPriorResetCoreSpecializedProbes) {
      break;  // LCOV_EXCL_LINE
    }

    // A core proved unreachable at an earlier reset step is only a candidate
    // here.  Re-prove it at the current target step before using it; this keeps
    // the shortcut an exact reset-image proof while avoiding the measured huge
    // LCOV_DISABLED_STOP
    // full-cube frontier SAT query.
    if (const auto conflict =  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            resetSpecializedConflictCubeAtStep(
                problem,
                transitionByState,
                // LCOV_DISABLED_STOP
                cache,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                candidate.core,
                targetStep,
                frameInvariant,
                // LCOV_DISABLED_STOP
                allowDeepSmallCubeRelaxedBudget);  // LCOV_EXCL_LINE
        conflict.has_value() && cubeContainsCube(cube, *conflict)) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      if (pdrStatsEnabled()) {
      // LCOV_DISABLED_STOP
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: prior reset core specialized conflict ",
            // LCOV_DISABLED_START
            "post_bootstrap_steps=", postBootstrapSteps,
            // LCOV_DISABLED_STOP
            " cube=", cube.size(),  // LCOV_EXCL_LINE
            " candidate=", candidate.core.size(),  // LCOV_EXCL_LINE
            "->", conflict->size(),  // LCOV_EXCL_LINE
            " known_step=", candidate.knownStep,
            // LCOV_DISABLED_START
            " probes=", probes,
            " hash=", cubeFingerprint(*conflict));
      }
      // LCOV_DISABLED_STOP
      return *conflict;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
  }
  return std::nullopt;  // LCOV_EXCL_LINE
}

std::optional<StateCube> memoizedResetSpecializedConflictCubeAtStep(  // LCOV_EXCL_LINE
// LCOV_DISABLED_STOP
    const ResetFrontierCache& cache,
    // LCOV_DISABLED_START
    const StateCube& cube,
    size_t targetStep,
    // LCOV_DISABLED_STOP
    BoolExpr* frameInvariant) {
  // LCOV_DISABLED_START
  StateCube queryCube = cube;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
  normalizeCube(queryCube);  // LCOV_EXCL_LINE
  const ResetExpressionConflictKey memoKey =
      resetExpressionConflictCacheKey(queryCube, targetStep, frameInvariant);  // LCOV_EXCL_LINE
  const auto* entry =  // LCOV_EXCL_LINE
      lookupResetExpressionConflictMemo(  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          cache.resetExpressionConflictByKey, memoKey);  // LCOV_EXCL_LINE
  if (entry == nullptr || !entry->hasConflict) {  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  // LCOV_DISABLED_START
  return entry->conflict;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> memoizedPriorResetCoreConflictAtStep(  // LCOV_EXCL_LINE
// LCOV_DISABLED_STOP
    const StateCube& cube,
    // LCOV_DISABLED_START
    size_t postBootstrapSteps,
    size_t targetStep,
    const ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
    // LCOV_DISABLED_STOP
  if (postBootstrapSteps == 0) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  std::vector<StateCube> conflicts;  // LCOV_EXCL_LINE
  for (const auto& [knownStep, cores] :  // LCOV_EXCL_LINE
       cache.resetUnreachableCoresByPostBootstrapStep) {  // LCOV_EXCL_LINE
       // LCOV_DISABLED_STOP
    if (knownStep >= postBootstrapSteps) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_START
    for (const StateCube& core : cores) {  // LCOV_EXCL_LINE
      if (core.empty() || core.size() >= cube.size() ||  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
          !cubeContainsCube(cube, core)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      if (const auto conflict =  // LCOV_EXCL_LINE
              memoizedResetSpecializedConflictCubeAtStep(  // LCOV_EXCL_LINE
                  cache, core, targetStep, frameInvariant);  // LCOV_EXCL_LINE
          conflict.has_value() && cubeContainsCube(cube, *conflict)) {  // LCOV_EXCL_LINE
        conflicts.push_back(*conflict);  // LCOV_EXCL_LINE
      }
    }
  }
  if (!conflicts.empty()) {  // LCOV_EXCL_LINE
    sortStateCubesDeterministically(conflicts);  // LCOV_EXCL_LINE
    return conflicts.front();  // LCOV_EXCL_LINE
  }
  return std::nullopt;  // LCOV_EXCL_LINE
// LCOV_DISABLED_START
}  // LCOV_EXCL_LINE
// LCOV_DISABLED_STOP

std::vector<size_t> predecessorProjectionSymbols(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    const std::vector<size_t>& transitionSupportSymbols,
    PdrFormulaSupportCache* supportCache) {
  if (supportCache == nullptr) {
    throw std::logic_error(  // LCOV_EXCL_LINE
        "PDR predecessor projection requires a formula support cache");  // LCOV_EXCL_LINE
  }
  // This routine runs for every predecessor query.  Reuse the resolver's
  // cached state-symbol set instead of rebuilding the large miter-state hash
  // table on each PDR obligation.
  const auto& stateSymbolSet = transitionByState.stateSymbols();

  std::unordered_set<size_t> projection;
  projection.reserve(transitionSupportSymbols.size());
  for (const auto supportSymbol : transitionSupportSymbols) {
    if (stateSymbolSet.find(supportSymbol) != stateSymbolSet.end()) {
      projection.insert(supportSymbol);
    }
  }
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Most SEC startup formulas are generated from explicit state
      // assignments/equalities.  Use those structured facts to pull in only
      // init partners relevant to the current transition cone; scanning the
      // full monolithic init BoolExpr here dominated large PDR predecessor
      // queries even though the query itself encoded only a small slice.
      addRelevantInitConstraintSymbols(problem, projection);
    } else {
      addFormulaStateSupport(initFormula, stateSymbolSet, projection, *supportCache);
    }
  } else {
    addRelevantFrameClauseSymbols(problem, frames[level], projection);
    addFormulaStateSupport(frameInvariant, stateSymbolSet, projection, *supportCache);
  }
  addRelevantComplementedStatePartners(complementPartners, projection);
  addRelevantSameFrameStateEqualityPartners(problem, projection);
  return sortUniqueSymbols(std::move(projection));
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
      if (!variables.hasSymbol(primarySymbol) ||
          !variables.hasSymbol(complementedSymbol)) {
        continue;
      }
      addLiteralEquivalence(
          solver,
          variables.getLiteral(complementedSymbol, frame),
          -variables.getLiteral(primarySymbol, frame));
    }
  }
}

void addSameFrameStateEqualities(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
      if (!variables.hasSymbol(lhsSymbol) || !variables.hasSymbol(rhsSymbol)) {
        continue;
      }
      addLiteralEquivalence(
          solver,
          variables.getLiteral(lhsSymbol, frame),
          variables.getLiteral(rhsSymbol, frame));
    }
  }
}

void addSameFrameStateEqualities(SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const KInductionProblem& problem,
                                 size_t numFrames) {
  addSameFrameStateEqualities(
      solver, variables, problem.sameFrameStateEqualityPairs0, numFrames);
  addSameFrameStateEqualities(
      solver, variables, problem.sameFrameStateEqualityPairs1, numFrames);
}

void addDualRailStateValidity(SATSolverWrapper& solver,
                              const FrameVariableStore& variables,
                              const std::vector<DualRailSymbolPair>& railPairs,
                              size_t numFrames) {
  for (size_t frame = 0; frame < numFrames; ++frame) {
    for (const auto& rails : railPairs) {
      if (!variables.hasSymbol(rails.mayBeOne) ||
          !variables.hasSymbol(rails.mayBeZero)) {
        continue;
      }
      // The dual-rail state space contains only 0, 1, and X.  PDR must block
      // and generalize over that legal state space, not over the empty value.
      solver.addClause({
          variables.getLiteral(rails.mayBeOne, frame),
          variables.getLiteral(rails.mayBeZero, frame)});
    }
  }
}

void normalizeCube(StateCube& cube) {
  // Canonical ordering lets us compare cubes structurally and avoid learning
  // the same obligation more than once with a different literal order.
  std::sort(cube.begin(), cube.end(), cubeLiteralLess);
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
}

void normalizeClause(StateClause& clause) {
  // Clauses are canonicalized for the same reason: later subsumption and
  // LCOV_DISABLED_START
  // convergence checks depend on stable ordering and deduplication.
  std::sort(clause.begin(), clause.end(), clauseLiteralLess);
  // LCOV_DISABLED_STOP
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

SymbolPair canonicalPair(size_t lhs, size_t rhs) {
  if (rhs < lhs) {
    std::swap(lhs, rhs);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return SymbolPair{lhs, rhs};
}

InitFactIndex buildInitFactIndex(const KInductionProblem& problem) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities =
      KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()
          ? (usesBootstrapFrontier ? problem.bootstrapStateEqualityPairs
                                   : problem.initialStateEqualityPairs)
          : emptySymbolPairs();

  InitFactIndex index;
  index.assignments.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    index.assignments.emplace(symbol, value);
    index.relations.ensureSymbol(symbol);
  }
  index.equalities.reserve(equalities.size());
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.sameFrameStateEqualityPairs0) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.sameFrameStateEqualityPairs1) {
    index.equalities.insert(canonicalPair(lhsSymbol, rhsSymbol));
    index.relations.addEquality(lhsSymbol, rhsSymbol);
  }
  index.complements.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       // LCOV_DISABLED_START
       problem.complementedStatePairs0) {
       // LCOV_DISABLED_STOP
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  index.rootAssignments.reserve(index.assignments.size());
  std::vector<std::pair<size_t, bool>> orderedAssignments(
      index.assignments.begin(), index.assignments.end());
  std::sort(orderedAssignments.begin(), orderedAssignments.end());
  for (const auto& [symbol, value] : orderedAssignments) {
    const auto root = index.relations.findWithParity(symbol);
    if (!root.has_value()) {
      continue;  // LCOV_EXCL_LINE
    }
    const bool rootValue = value ^ root->second;
    if (const auto it = index.rootAssignments.find(root->first);
        it == index.rootAssignments.end()) {
      index.rootAssignments.emplace(root->first, rootValue);
    }
  }
  return index;
}

std::optional<StateCube> knownInitConflictCube(const InitFactIndex& facts,
                                               const StateCube& cube) {
  // PDR frequently reaches a level-0 cube that is impossible only because it
  // violates a startup equality such as "state0 == state1".  Learning the full
  // LCOV_DISABLED_START
  // 100+ literal cube makes the engine enumerate many adjacent impossible
  // LCOV_DISABLED_STOP
  // startup states.  This extractor turns the visible conflict into the
  // smallest safe cube:
  // LCOV_DISABLED_START
  //   - one literal for an init assignment conflict;
  //   - two literals for equality/complement conflicts.
  // The learned clause is still exactly an Init consequence, but much stronger.
  std::unordered_map<size_t, std::pair<bool, CubeLiteral>> cubeValueByRoot;
  // LCOV_DISABLED_STOP
  cubeValueByRoot.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto root = facts.relations.findWithParity(literal.symbol);
    if (!root.has_value()) {
      const auto assignment = facts.assignments.find(literal.symbol);
      // LCOV_DISABLED_START
      if (assignment == facts.assignments.end() ||
          assignment->second == literal.value) {  // LCOV_EXCL_LINE
        continue;
      }
      // LCOV_DISABLED_STOP
      StateCube conflict{literal};  // LCOV_EXCL_LINE
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      return conflict;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }  // LCOV_EXCL_LINE

    const bool rootValue = literal.value ^ root->second;
    const auto assignment = facts.rootAssignments.find(root->first);
    if (assignment != facts.rootAssignments.end() &&
        assignment->second != rootValue) {
        // LCOV_DISABLED_STOP
      StateCube conflict{literal};  // LCOV_EXCL_LINE
      normalizeCube(conflict);  // LCOV_EXCL_LINE
      return conflict;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    if (const auto it = cubeValueByRoot.find(root->first);
        it != cubeValueByRoot.end()) {
      if (it->second.first != rootValue) {  // LCOV_EXCL_LINE
        StateCube conflict{it->second.second, literal};  // LCOV_EXCL_LINE
        normalizeCube(conflict);  // LCOV_EXCL_LINE
        return conflict;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_START
    cubeValueByRoot.emplace(root->first, std::pair{rootValue, literal});
  }
  // LCOV_DISABLED_STOP

  return std::nullopt;
}

// LCOV_DISABLED_START

bool twoLiteralCubeIsKnownOutsideInit(const InitFactIndex& facts,
// LCOV_DISABLED_STOP
                                      size_t lhsSymbol,
                                      bool lhsValue,
                                      size_t rhsSymbol,
                                      bool rhsValue) {
  if (const auto lhsAssignment = facts.assignments.find(lhsSymbol);
      lhsAssignment != facts.assignments.end() &&
      lhsAssignment->second != lhsValue) {  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
  }
  if (const auto rhsAssignment = facts.assignments.find(rhsSymbol);
      rhsAssignment != facts.assignments.end() &&
      rhsAssignment->second != rhsValue) {  // LCOV_EXCL_LINE
    return true;  // LCOV_EXCL_LINE
  }
  const auto lhsRoot = facts.relations.findWithParity(lhsSymbol);
  const auto rhsRoot = facts.relations.findWithParity(rhsSymbol);
  if (!lhsRoot.has_value() || !rhsRoot.has_value() ||
      lhsRoot->first != rhsRoot->first) {  // LCOV_EXCL_LINE
    return false;
  }
  return (lhsValue ^ lhsRoot->second) != (rhsValue ^ rhsRoot->second);  // LCOV_EXCL_LINE
}

StateClause clauseFromCube(const StateCube& cube) {
  StateClause clause;
  clause.reserve(cube.size());
  for (const auto& literal : cube) {
    clause.push_back({literal.symbol, !literal.value});
  }
  normalizeClause(clause);
  return clause;
}

StateCube cubeFromClauseNegation(const StateClause& clause) {
  StateCube cube;
  cube.reserve(clause.size());
  for (const auto& literal : clause) {
    cube.push_back({literal.symbol, !literal.positive});
  }
  normalizeCube(cube);
  return cube;
}

bool clauseSubsumes(const StateClause& lhs, const StateClause& rhs) {
  return std::includes(rhs.begin(), rhs.end(), lhs.begin(), lhs.end(),
                       [](const ClauseLiteral& a, const ClauseLiteral& b) {
                         if (a.symbol != b.symbol) {
                           return a.symbol < b.symbol;
                         }
                         return a.positive < b.positive;
                       });
}

bool frameHasSubsumingClause(const FrameClauses& frame, const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    if (clauseSubsumes(existingClause, clause)) {
      return true;
    }
  }
  return false;
}

std::optional<StateClause> findSubsumingFrameClause(
    const FrameClauses& frame,
    const StateClause& clause) {
  for (const auto& existingClause : frame.clauses) {
    if (clauseSubsumes(existingClause, clause)) {
      return existingClause;
    }
  }
  return std::nullopt;
}

bool addClauseToFrame(FrameClauses& frame, StateClause clause) {
  normalizeClause(clause);
  if (frameHasSubsumingClause(frame, clause)) {
    return false;
  }

  // Keep each frame minimal so later SAT queries do not carry redundant facts.
  frame.clauses.erase(
      std::remove_if(
          frame.clauses.begin(),
          frame.clauses.end(),
          [&](const StateClause& existingClause) {
            return clauseSubsumes(clause, existingClause);
          }),
      frame.clauses.end());
  frame.addedClauseLog.push_back(clause);
  // The remaining clauses stay sorted after erase(), so a lower_bound insert
  // preserves the deterministic frame order without resorting the whole frame
  // for every learned clause.
  auto insertPosition =
      std::lower_bound(frame.clauses.begin(), frame.clauses.end(), clause,
                       stateClauseLess);
  frame.clauses.insert(insertPosition, std::move(clause));
  frame.clauseIndexDirty = true;
  frame.clauseEmitEpochByIndex.clear();
  return true;
}

bool addClauseToFrames(std::vector<FrameClauses>& frames,
                       const StateClause& clause,
                       size_t maxLevel) {
  bool addedAny = false;
  for (size_t level = 1; level <= maxLevel; ++level) {
    addedAny = addClauseToFrame(frames[level], clause) || addedAny;
  }
  return addedAny;
}  // LCOV_EXCL_LINE

size_t validatedBadFormulaCnfSupportLimit(const KInductionProblem& problem) {
  // Dual rail represents one ternary state bit with two Boolean rails.  Keep
  // the binary SEC limit unchanged, but allow the same small logical support
  // after rail expansion so PDR can learn local bad-formula clauses instead of
  // rediscovering sibling rail assignments one cube at a time.
  return problem.usesDualRailStateEncoding
             ? kMaxDualRailValidatedBadFormulaCnfSupport
             : kMaxValidatedBadFormulaCnfSupport;
}

size_t singleOutputBadFormulaClauseLimit(const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding
             ? kMaxDualRailSingleOutputExactValidatedBadFormulaClauses
             : kMaxSingleOutputExactValidatedBadFormulaClauses;
}

size_t exactResetCubeBadFormulaClauseLimit(const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding
             ? kMaxDualRailExactResetCubeValidatedBadFormulaClauses
             : kMaxExactResetCubeValidatedBadFormulaClauses;
}

bool hasLargeDualRailResetFrontierSurface(const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding &&
         // LCOV_DISABLED_START
         (pdrDualRailStateSymbolCount(problem) >
         // LCOV_DISABLED_STOP
              dualRailResetFrontierStateSymbolLimit() ||
          // LCOV_DISABLED_START
          pdrTransitionSourceCount(problem) >
          // LCOV_DISABLED_STOP
              dualRailResetFrontierTransitionSourceLimit() ||
          // A one-output leaf from a medium interface should still be allowed
          // to use local reset/bad-formula repair.  The current-slice cap keeps
          // broad reset-frontier queries out of PDR; the original-output cap
          // only prevents this repair from re-entering SoC-scale surfaces.
          pdrOriginalObservedOutputCount(problem) >
              kMaxExactResetFrontierDualRailOriginalOutputs);
}

template <typename Container>
void clearAndReleaseContainer(Container& container) {
  Container empty;
  container.swap(empty);
}

void releaseAllocatorFreePages() {
#if defined(__APPLE__)
  malloc_zone_pressure_relief(malloc_default_zone(), 0);
#elif defined(__GLIBC__)
  malloc_trim(0);
#endif
}

void releaseLargeDualRailResetFrontierContext(ResetFrontierCache& cache,
                                              const KInductionProblem& problem,
                                              std::string_view reason) {
  if (!hasLargeDualRailResetFrontierSurface(problem)) {
    return;
  }
  const bool hadReachabilityContext = cache.reachabilityContext != nullptr;
  const bool hadResetExpressionEvaluator =
      cache.resetExpressionEvaluator != nullptr;
  const bool hadResetExpressionCanonicalizer =
      cache.resetExpressionCanonicalizer != nullptr;
  const bool hadResetBootstrapExpressionRelations =
      cache.resetBootstrapExpressionRelations != nullptr;
  const size_t resetExpressionConflictMemos =
      cache.resetExpressionConflictByKey.size();
  const size_t resetExpressionBudgetSkips =
      cache.resetExpressionBudgetSkipFromStep.size();
  const size_t wholeBadFormulaMisses =
      cache.wholeBadFormulaValidationMisses.size();
  const size_t observedBadClauseGroups =
      cache.observedOutputBadClauseGroups.size();
  const size_t observedBadClauses =
      cache.observedOutputBadClauses.has_value()
          ? cache.observedOutputBadClauses->size()
          : 0;
  size_t lazyRemappedTransitions = 0;
  size_t lazyRemapMemoEntries = 0;
  size_t lazyDualRailRemapMemoEntries = 0;
  size_t lazySupportEntries = 0;
  size_t lazyNodeCountEntries = 0;
  size_t lazyStateEqualitySubsetEntries = 0;

  cache.reachabilityContext.reset();
  cache.resetExpressionEvaluator.reset();
  cache.resetExpressionProblem = nullptr;
  cache.resetExpressionTransitions = nullptr;
  cache.resetExpressionCanonicalizer.reset();
  cache.resetExpressionCanonicalizerProblem = nullptr;
  cache.resetBootstrapExpressionRelations.reset();
  cache.resetBootstrapExpressionProblem = nullptr;
  cache.resetBootstrapExpressionTransitions = nullptr;
  clearAndReleaseContainer(cache.resetExpressionConflictByKey);
  clearAndReleaseContainer(cache.resetExpressionBudgetSkipFromStep);
  clearAndReleaseContainer(cache.wholeBadFormulaValidationMisses);
  clearAndReleaseContainer(cache.observedOutputBadClauseGroups);
  cache.observedOutputBadClauses.reset();
  cache.observedOutputBadClauseCacheBuilt = false;

  if (problem.lazyTransitions != nullptr) {
    auto& store = *problem.lazyTransitions;
    lazyRemappedTransitions = store.remappedByStateSymbol.size();
    for (const auto& memo : store.remapMemoByDesign) {
      lazyRemapMemoEntries += memo.size();
    }
    for (const auto& memo : store.dualRailRemapMemoByDesign) {
      lazyDualRailRemapMemoEntries += memo.size();
    }
    lazySupportEntries = store.supportByStateSymbol.size();
    lazyNodeCountEntries = store.nodeCountByStateSymbol.size();
    lazyStateEqualitySubsetEntries = store.pdrStateEqualitySubsetCache.size();

    clearAndReleaseContainer(store.remappedByStateSymbol);
    for (auto& memo : store.remapMemoByDesign) {
      clearAndReleaseContainer(memo);
    }
    for (auto& memo : store.dualRailRemapMemoByDesign) {
      clearAndReleaseContainer(memo);
    }
    // Keep lazy support and node-count metadata across output-batched PDR
    // slices.  These caches contain compact COI facts, not materialized
    // transition expressions, and Swerv rebuilds them for many sibling
    // dual-rail leaves when they are released with the heavy remap caches.
    clearAndReleaseContainer(store.pdrStateEqualitySubsetCache);
  }

  releaseAllocatorFreePages();
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: released large dual-rail reset-frontier memory ",
        "reason=", reason,
        " rail_state_symbols=", pdrDualRailStateSymbolCount(problem),
        " transition_sources=", pdrTransitionSourceCount(problem),
        " context=", hadReachabilityContext ? 1 : 0,
        " reset_eval=", hadResetExpressionEvaluator ? 1 : 0,
        " canonicalizer=", hadResetExpressionCanonicalizer ? 1 : 0,
        " bootstrap_relations=",
        hadResetBootstrapExpressionRelations ? 1 : 0,
        " reset_expr_memos=", resetExpressionConflictMemos,
        " reset_expr_budget_skips=", resetExpressionBudgetSkips,
        " whole_bad_misses=", wholeBadFormulaMisses,
        " observed_bad_groups=", observedBadClauseGroups,
        " observed_bad_clauses=", observedBadClauses,
        " lazy_remapped=", lazyRemappedTransitions,
        " lazy_remap_memos=", lazyRemapMemoEntries,
        " lazy_dual_rail_memos=", lazyDualRailRemapMemoEntries,
        " lazy_support=", lazySupportEntries,
        " lazy_node_counts=", lazyNodeCountEntries,
        " lazy_state_eq_subsets=", lazyStateEqualitySubsetEntries);
  }
}

bool useResetFrontierPostBootstrapPrechecks(
    const KInductionProblem& problem,
    size_t postBootstrapSteps,
    bool requested,
    std::string_view reason) {
  if (!requested || postBootstrapSteps == 0) {
    return requested;
  }
  if (!hasLargeDualRailResetFrontierSurface(problem)) {
    return true;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: skipped large dual-rail reset-frontier precheck ",
        "reason=", reason,
        " post_bootstrap_steps=", postBootstrapSteps,
        " rail_state_symbols=", pdrDualRailStateSymbolCount(problem),
        " transition_sources=", pdrTransitionSourceCount(problem));
  }
  return false;
}

bool freshLargeDualRailExactResetFrontierQueryTooDeep(
    const KInductionProblem& problem,
    size_t postBootstrapSteps) {
  return hasLargeDualRailResetFrontierSurface(problem) &&
         postBootstrapSteps >
             kMaxFreshLargeDualRailExactResetFrontierPostBootstrapStep;
}

bool freshLargeDualRailSingletonResetFrontierQueryTooDeep(
    const KInductionProblem& problem,
    size_t postBootstrapSteps) {
  return hasLargeDualRailResetFrontierSurface(problem) &&
         postBootstrapSteps >
             kMaxFreshLargeDualRailSingletonResetFrontierPostBootstrapStep;
}

void emitSkippedFreshLargeDualRailExactResetFrontierQuery(
    const KInductionProblem& problem,
    const StateCube& cube,
    size_t postBootstrapSteps,
    std::string_view reason) {
  if (!pdrStatsEnabled()) {
    return;
  }
  emitSecDiag(
      "SEC PDR stats: skipped fresh large dual-rail exact reset-frontier query ",
      "reason=", reason,
      " post_bootstrap_steps=", postBootstrapSteps,
      " cube=", cube.size(),
      " rail_state_symbols=", pdrDualRailStateSymbolCount(problem),
      " transition_sources=", pdrTransitionSourceCount(problem),
      " hash=", cubeFingerprint(cube));
}

void releaseLargeDualRailPdrTransientCaches(
    ResetFrontierCache& resetCache,
    BadCubeAssumptionCache* badCubeCache,
    PredecessorAssumptionCache* predecessorCache,
    PdrFormulaSupportCache* supportCache,
    const KInductionProblem& problem,
    std::string_view reason) {
  if (!hasLargeDualRailResetFrontierSurface(problem)) {
    return;
  }

  const bool hadBadCubeSolver =
      badCubeCache != nullptr && badCubeCache->solver != nullptr;
  const size_t badCubeEncodedRoots =
      hadBadCubeSolver ? badCubeCache->solver->encodedBadRoots.size() : 0;
  const size_t badCubeQuerySymbols =
      hadBadCubeSolver ? badCubeCache->solver->querySymbolSet.size() : 0;
  const bool hadPredecessorSolver =
      predecessorCache != nullptr && predecessorCache->solver != nullptr;
  const size_t predecessorAssumptionLiterals =
      hadPredecessorSolver
          ? predecessorCache->solver->assumptionByTransitionLiteral.size()
          : 0;
  const size_t memoizedSupports =
      supportCache != nullptr ? supportCache->clearMemoizedSupports() : 0;

  if (badCubeCache != nullptr) {
    badCubeCache->solver.reset();
  }
  if (predecessorCache != nullptr) {
    predecessorCache->solver.reset();
  }
  releaseLargeDualRailResetFrontierContext(resetCache, problem, reason);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: released large dual-rail PDR transient caches ",
        "reason=", reason,
        " bad_solver=", hadBadCubeSolver ? 1 : 0,
        " bad_roots=", badCubeEncodedRoots,
        " bad_symbols=", badCubeQuerySymbols,
        " predecessor_solver=", hadPredecessorSolver ? 1 : 0,
        " predecessor_assumptions=", predecessorAssumptionLiterals,
        " memoized_supports=", memoizedSupports);
  }
}

struct LargeDualRailPdrTransientCacheReleaseGuard {
  ResetFrontierCache& resetCache;
  BadCubeAssumptionCache& badCubeCache;
  PredecessorAssumptionCache& predecessorCache;
  PdrFormulaSupportCache& supportCache;
  const KInductionProblem& problem;
  BoolExpr* frameInvariant = nullptr;

  ~LargeDualRailPdrTransientCacheReleaseGuard() {
    rememberProcessResetUnreachableCores(
        problem, resetCache, frameInvariant);
    releaseLargeDualRailPdrTransientCaches(
        resetCache,
        &badCubeCache,
        &predecessorCache,
        &supportCache,
        problem,
        "pdr_run_exit");
  }
};

bool canExactlyValidateBadFormulaGroup(const KInductionProblem& problem,
                                       size_t targetFrame,
                                       const std::vector<StateClause>& clauses) {
  return targetFrame <= 1 &&
         clauses.size() <= exactResetCubeBadFormulaClauseLimit(problem);
}

// LCOV_DISABLED_START
size_t partialTargetResetFrontierBadFormulaCheapCheckLimit(  // LCOV_EXCL_LINE
// LCOV_DISABLED_STOP
    const KInductionProblem& problem) {
  return problem.usesDualRailStateEncoding  // LCOV_EXCL_LINE
             ? kMaxDualRailPartialTargetResetFrontierBadFormulaCheapChecks
             : kMaxPartialTargetResetFrontierBadFormulaCheapChecks;
}

void emitSkippedPerOutputBadFormulaGroupDiag(
    size_t targetFrame,
    const ObservedOutputBadClauseGroup& group,
    std::string_view reason,
    size_t limit = 0) {
  if (!pdrStatsEnabled()) {
    return;  // LCOV_EXCL_LINE
  }
  emitSecDiag(
      // LCOV_DISABLED_START
      "SEC PDR stats: skipped per-output bad-formula validation ",
      // LCOV_DISABLED_STOP
      "bad_frame=", targetFrame,
      " output=", group.outputIndex,
      " clauses=", group.clauses.size(),
      " reason=", reason,
      // LCOV_DISABLED_START
      " limit=", limit);
      // LCOV_DISABLED_STOP
}

std::optional<std::vector<StateClause>> stateOnlyBadFormulaClauses(
    // LCOV_DISABLED_START
    BoolExpr* badFormula,
    // LCOV_DISABLED_STOP
    const std::unordered_set<size_t>& stateSymbols,
    size_t supportLimit) {
  if (badFormula == nullptr) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  const auto supportSet = badFormula->getSupportVars();
  if (supportSet.size() > supportLimit) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : supportSet) {
    if (stateSymbols.find(symbol) == stateSymbols.end()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  std::vector<size_t> support(supportSet.begin(), supportSet.end());
  std::vector<StateClause> clauses;
  const size_t assignmentCount = static_cast<size_t>(1) << support.size();
  clauses.reserve(assignmentCount);
  for (size_t mask = 0; mask < assignmentCount; ++mask) {
    std::unordered_map<size_t, bool> env;
    env.reserve(support.size());
    for (size_t bit = 0; bit < support.size(); ++bit) {
      env.emplace(support[bit], ((mask >> bit) & 1u) != 0u);
    }
    if (!badFormula->evaluate(env)) {
      continue;
    }

    StateClause clause;
    clause.reserve(support.size());
  for (const auto symbol : support) {
      const bool value = env.at(symbol);
      // Forbid exactly this bad assignment.
      clause.push_back({symbol, !value});
    }
    normalizeClause(clause);
    // LCOV_DISABLED_START
    clauses.push_back(std::move(clause));
    // LCOV_DISABLED_STOP
  }
  sortStateClausesDeterministically(clauses);
  return clauses;
// LCOV_DISABLED_START
}
// LCOV_DISABLED_STOP

bool appendStateOnlyBadFormulaClauses(
    std::vector<StateClause>& target,
    BoolExpr* badFormula,
    const std::unordered_set<size_t>& stateSymbols,
    size_t supportLimit) {
  const auto clauses =
      stateOnlyBadFormulaClauses(badFormula, stateSymbols, supportLimit);
  if (!clauses.has_value() || clauses->empty()) {
    return false;  // LCOV_EXCL_LINE
  }
  if (target.size() + clauses->size() > kMaxValidatedBadFormulaClauses) {
    return false;  // LCOV_EXCL_LINE
  }
  target.insert(target.end(), clauses->begin(), clauses->end());
  return true;
}

std::vector<ObservedOutputBadClauseGroup> observedOutputBadFormulaClauseGroups(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& stateSymbols) {
  if (problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return {};
  }

  std::vector<ObservedOutputBadClauseGroup> groups;
  const size_t supportLimit = validatedBadFormulaCnfSupportLimit(problem);
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    BoolExpr* outputBad = BoolExpr::simplify(
        BoolExpr::Xor(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
    // A rejected batched SEC counterexample proves the OR of output mismatches
    // unreachable at this frame. Therefore each small state-only disjunct can
    // be learned independently, while unsupported or too-wide disjuncts simply
    // remain for normal PDR search.
    std::vector<StateClause> clauses;
    appendStateOnlyBadFormulaClauses(
        clauses, outputBad, stateSymbols, supportLimit);
    if (!clauses.empty()) {
      groups.push_back(ObservedOutputBadClauseGroup{
          output, outputBad, std::move(clauses)});
    }
  }
  return groups;
}

std::optional<std::vector<StateClause>> observedOutputBadFormulaClausesFromGroups(
    const std::vector<ObservedOutputBadClauseGroup>& groups);

std::optional<std::vector<StateClause>> observedOutputBadFormulaClauses(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& stateSymbols) {
  const auto groups = observedOutputBadFormulaClauseGroups(problem, stateSymbols);
  return observedOutputBadFormulaClausesFromGroups(groups);
}

std::optional<std::vector<StateClause>> observedOutputBadFormulaClausesFromGroups(
    // LCOV_DISABLED_START
    const std::vector<ObservedOutputBadClauseGroup>& groups) {
    // LCOV_DISABLED_STOP
  if (groups.empty()) {
    return std::nullopt;
  }

  std::vector<StateClause> clauses;
  for (const auto& group : groups) {
    clauses.insert(clauses.end(), group.clauses.begin(), group.clauses.end());
    if (clauses.size() >= kMaxValidatedBadFormulaClauses) {
      break;  // LCOV_EXCL_LINE
    }
  }
  if (clauses.empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  sortStateClausesDeterministically(clauses);
  return clauses;
}

void ensureObservedOutputBadClauseCache(
    ResetFrontierCache& resetFrontierCache,
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& stateSymbols) {
  if (resetFrontierCache.observedOutputBadClauseCacheBuilt) {
    return;
  }
  resetFrontierCache.observedOutputBadClauseGroups =
      observedOutputBadFormulaClauseGroups(problem, stateSymbols);
  resetFrontierCache.observedOutputBadClauses =
      observedOutputBadFormulaClausesFromGroups(
          resetFrontierCache.observedOutputBadClauseGroups);
  resetFrontierCache.observedOutputBadClauseCacheBuilt = true;
}

bool hasNewValidatedBadFormulaClause(
    const std::vector<FrameClauses>& frames,
    const std::vector<StateClause>& clauses,
    size_t targetFrame) {
  for (const auto& clause : clauses) {
    StateClause normalizedClause = clause;
    normalizeClause(normalizedClause);
    for (size_t level = 1; level <= targetFrame && level < frames.size(); ++level) {
      // LCOV_DISABLED_START
      if (!frameHasSubsumingClause(frames[level], normalizedClause)) {
      // LCOV_DISABLED_STOP
        return true;
      }
    }
  }
  return false;
}

bool hasNewValidatedBadFormulaClauseAtFrame(
    // LCOV_DISABLED_START
    const std::vector<FrameClauses>& frames,
    // LCOV_DISABLED_STOP
    const std::vector<StateClause>& clauses,
    size_t targetFrame) {
  if (targetFrame >= frames.size()) {
    return false;  // LCOV_EXCL_LINE
  }
  for (const auto& clause : clauses) {
    StateClause normalizedClause = clause;
    normalizeClause(normalizedClause);
    if (!frameHasSubsumingClause(frames[targetFrame], normalizedClause)) {
      return true;
    }
  }
  return false;  // LCOV_EXCL_LINE
}

StateCube cubeForbiddenByStateClause(const StateClause& clause) {
  StateCube cube;
  cube.reserve(clause.size());
  for (const auto& literal : clause) {
    // A learned bad-formula clause is the negation of one bad state
    // assignment. Flip each literal back to the concrete bad cube that must be
    // proven unreachable before the clause can be learned.
    cube.push_back({literal.symbol, !literal.positive});
  }
  normalizeCube(cube);
  return cube;
}

StateCube validationSupportCubeForStateClauses(
    const std::vector<StateClause>& clauses) {
  StateCube validationSupportCube;
  std::unordered_set<size_t> validationSupportSymbols;
  for (const auto& clause : clauses) {
    for (const auto& literal : cubeForbiddenByStateClause(clause)) {
      if (validationSupportSymbols.insert(literal.symbol).second) {
        validationSupportCube.push_back(literal);
      }
    }
  }
  normalizeCube(validationSupportCube);
  return validationSupportCube;
}

StateClauseSetKey badFormulaValidationCacheKey(
    const std::vector<StateClause>& clauses,
    size_t targetFrame) {
  StateClauseSetKey key;
  key.targetFrame = targetFrame;
  key.clauses = clauses;
  return key;
// LCOV_DISABLED_START
}


// LCOV_DISABLED_STOP
size_t countCachedResetValidatedBadFormulaAssignments(  // LCOV_EXCL_LINE
    const std::vector<StateClause>& clauses,
    // LCOV_DISABLED_START
    size_t targetFrame,
    // LCOV_DISABLED_STOP
    const ResetFrontierCache& resetFrontierCache) {
  size_t count = 0;  // LCOV_EXCL_LINE
  for (const auto& clause : clauses) {  // LCOV_EXCL_LINE
    if (findPdrResetUnreachableCoreForCube(  // LCOV_EXCL_LINE
            resetFrontierCache,  // LCOV_EXCL_LINE
            cubeForbiddenByStateClause(clause),  // LCOV_EXCL_LINE
            targetFrame)  // LCOV_EXCL_LINE
        .has_value()) {  // LCOV_EXCL_LINE
      ++count;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }  // LCOV_EXCL_LINE
  }
  return count;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

bool frameInvariantImpliesClauses(
    BoolExpr* frameInvariant,
    // LCOV_DISABLED_STOP
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<StateClause>& clauses) {
  if (frameInvariant == nullptr || clauses.empty()) {
    // LCOV_DISABLED_START
    return false;
  }

  const auto invariantSupport = frameInvariant->getSupportVars();  // LCOV_EXCL_LINE
  for (const auto& clause : clauses) {  // LCOV_EXCL_LINE
    std::unordered_set<size_t> querySymbols(  // LCOV_EXCL_LINE
        invariantSupport.begin(), invariantSupport.end());  // LCOV_EXCL_LINE
    const StateCube forbiddenCube = cubeForbiddenByStateClause(clause);  // LCOV_EXCL_LINE
    for (const auto& literal : forbiddenCube) {  // LCOV_EXCL_LINE
      querySymbols.insert(literal.symbol);  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }

// LCOV_DISABLED_START

    const std::vector<size_t> solverSymbols =
    // LCOV_DISABLED_STOP
        sortUniqueSymbols(std::move(querySymbols));  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    SATSolverWrapper solver(solverType);  // LCOV_EXCL_LINE
    solver.configureForSecPdrQuery(solverSymbols.size());  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    FrameVariableStore variables(solver, solverSymbols, 1);  // LCOV_EXCL_LINE
    FrameFormulaEncoder encoder(  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        solver, variables.makeLeafLits(0, invariantSupport));  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
    solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    for (const auto& literal : forbiddenCube) {  // LCOV_EXCL_LINE
      const int satLiteral = variables.getLiteral(literal.symbol, 0);  // LCOV_EXCL_LINE
      solver.addClause({literal.value ? satLiteral : -satLiteral});  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_STOP
    if (solver.solve()) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      return false;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_STOP
  }  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}

std::vector<std::vector<std::pair<size_t, bool>>> forbiddenAssignmentCubes(  // LCOV_EXCL_LINE
    const std::vector<StateClause>& clauses) {
  std::vector<std::vector<std::pair<size_t, bool>>> cubes;  // LCOV_EXCL_LINE
  cubes.reserve(clauses.size());  // LCOV_EXCL_LINE
  for (const auto& clause : clauses) {  // LCOV_EXCL_LINE
    cubes.push_back(cubeAssignments(cubeForbiddenByStateClause(clause)));  // LCOV_EXCL_LINE
  }
  return cubes;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<bool> validateBadFormulaClausesWithResetCubes(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    // LCOV_DISABLED_START
    const std::vector<StateClause>& clauses,
    size_t targetFrame,
    ResetFrontierCache& resetFrontierCache,
    std::vector<FrameClauses>* frames = nullptr,
    size_t* learnedResetConflictClausesOut = nullptr,
    bool allowExactResetFrontierQueries = true) {
  if (learnedResetConflictClausesOut != nullptr) {
    *learnedResetConflictClausesOut = 0;
  }
  if (problem.resetBootstrapCycles == 0 || targetFrame == 0) {
    return std::nullopt;
  }
  const StateCube validationSupportCube =
      validationSupportCubeForStateClauses(clauses);  // LCOV_EXCL_LINE
  const bool deepLocalResetSpecializedRepair =  // LCOV_EXCL_LINE
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&  // LCOV_EXCL_LINE
      targetFrame <=  // LCOV_EXCL_LINE
          kMaxFreshDeepResetSpecializedBadFormulaRepairFrame &&  // LCOV_EXCL_LINE
      !allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
      clauses.size() <=  // LCOV_EXCL_LINE
          kMaxDeepLocalExactResetCubeValidatedBadFormulaClauses &&  // LCOV_EXCL_LINE
      !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport;  // LCOV_EXCL_LINE
  const bool deepResetSpecializedOnlyRepair =  // LCOV_EXCL_LINE
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&  // LCOV_EXCL_LINE
      !allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
      !deepLocalResetSpecializedRepair;  // LCOV_EXCL_LINE
  const bool deepLocalExactResetValidation =  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&  // LCOV_EXCL_LINE
      allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
      clauses.size() <=  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          kMaxDeepLocalExactResetCubeValidatedBadFormulaClauses &&  // LCOV_EXCL_LINE
      !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport;  // LCOV_EXCL_LINE
  if (targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
      clauses.size() > kMaxExactResetCubeValidatedBadFormulaClauses &&  // LCOV_EXCL_LINE
      !deepResetSpecializedOnlyRepair &&  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      !deepLocalExactResetValidation &&  // LCOV_EXCL_LINE
      !deepLocalResetSpecializedRepair) {  // LCOV_EXCL_LINE
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: skipped deep reset-specialized bad-formula "
          "validation ",
          "bad_frame=", targetFrame,
          " clauses=", clauses.size(),  // LCOV_EXCL_LINE
          " support=", validationSupportCube.size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
  }

// LCOV_DISABLED_START

  if (allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
      !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport) {  // LCOV_EXCL_LINE
    auto& reachabilityContext = resetReachabilityContextFor(  // LCOV_EXCL_LINE
        resetFrontierCache, problem, transitionByState, nullptr);  // LCOV_EXCL_LINE
    primeResetFrontierReachabilitySolver(  // LCOV_EXCL_LINE
        reachabilityContext,  // LCOV_EXCL_LINE
        solverType,  // LCOV_EXCL_LINE
        cubeAssignments(validationSupportCube),  // LCOV_EXCL_LINE
        targetFrame);  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  size_t checkedClauses = 0;  // LCOV_EXCL_LINE
  size_t deepResetSpecializedClauseChecks = 0;  // LCOV_EXCL_LINE
  size_t learnedResetConflictClauses = 0;  // LCOV_EXCL_LINE
  size_t learnedFreshResetConflictClauses = 0;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
  size_t skippedDeepResetSpecializedProbes = 0;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  size_t freshResetSpecializedProbes = 0;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
  std::vector<StateCube> residualExactValidationCubes;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  bool residualExactValidationOverflow = false;  // LCOV_EXCL_LINE
  const bool allowResidualExactBatch =  // LCOV_EXCL_LINE
      canUseResidualExactResetCubeBatch(problem);  // LCOV_EXCL_LINE
  const bool deepPartialResetRepair =  // LCOV_EXCL_LINE
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      !allowExactResetFrontierQueries;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  auto rememberResidualExactValidationCube = [&](const StateCube& cube) {  // LCOV_EXCL_LINE
    if (!allowResidualExactBatch ||  // LCOV_EXCL_LINE
        allowExactResetFrontierQueries ||  // LCOV_EXCL_LINE
        targetFrame >  // LCOV_EXCL_LINE
            kMaxResidualExactResetCubeValidatedBadFormulaFrame ||  // LCOV_EXCL_LINE
        validationSupportCube.size() > kMaxResetCubeValidationPrimeSupport) {  // LCOV_EXCL_LINE
      return;  // LCOV_EXCL_LINE
    }
    if (residualExactValidationCubes.size() <  // LCOV_EXCL_LINE
        kMaxResidualExactResetCubeValidatedBadFormulaClauses) {
        // LCOV_DISABLED_STOP
      residualExactValidationCubes.push_back(cube);  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    } else {  // LCOV_EXCL_LINE
      residualExactValidationOverflow = true;  // LCOV_EXCL_LINE
    }
  };  // LCOV_EXCL_LINE
  auto learnResetConflict = [&](StateCube conflict) -> bool {  // LCOV_EXCL_LINE
    normalizeCube(conflict);  // LCOV_EXCL_LINE
    rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
        resetFrontierCache,  // LCOV_EXCL_LINE
        problem,  // LCOV_EXCL_LINE
        transitionByState,  // LCOV_EXCL_LINE
        conflict,  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
        targetFrame,  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        nullptr);
        // LCOV_DISABLED_STOP
    bool learnedFrameClause = false;  // LCOV_EXCL_LINE
    if (frames != nullptr && targetFrame < frames->size() &&  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        addClauseToFrame((*frames)[targetFrame], clauseFromCube(conflict))) {  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
      ++learnedResetConflictClauses;  // LCOV_EXCL_LINE
      learnedFrameClause = true;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    return learnedFrameClause;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  };  // LCOV_EXCL_LINE
  auto reachedDeepPartialRepairBudget = [&]() {  // LCOV_EXCL_LINE
    if (!deepPartialResetRepair) {  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }
    if (deepResetSpecializedOnlyRepair) {  // LCOV_EXCL_LINE
      // This path is cache-only: no fresh reset-image SAT query is opened, so
      // LCOV_DISABLED_START
      // draining a batch is the fastest way to avoid rediscovering siblings.
      return learnedResetConflictClauses >=  // LCOV_EXCL_LINE
             kMaxDeepCacheOnlyResetConflictClausesPerRepair;
             // LCOV_DISABLED_STOP
    }
    // LCOV_DISABLED_START
    return learnedFreshResetConflictClauses >=  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
           kMaxDeepPartialFreshResetConflictClausesPerRepair;
  // LCOV_DISABLED_START
  };  // LCOV_EXCL_LINE
  auto reachedNonExactFreshResetProbeBudget = [&]() {  // LCOV_EXCL_LINE
  // LCOV_DISABLED_STOP
    return !allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
           freshResetSpecializedProbes >=  // LCOV_EXCL_LINE
               // LCOV_DISABLED_START
               kMaxNonExactFreshResetSpecializedProbesPerRepair;
  };
  auto scopedBadFormulaResetBudget =
      [&]() -> std::optional<ScopedResetSymbolicEvaluatorBudget> {  // LCOV_EXCL_LINE
    if (allowExactResetFrontierQueries) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    return std::optional<ScopedResetSymbolicEvaluatorBudget>{  // LCOV_EXCL_LINE
        std::in_place,
        resetSymbolicEvaluatorFor(  // LCOV_EXCL_LINE
            resetFrontierCache, problem, transitionByState),  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
        kMaxBadFormulaRepairResetSymbolicStates,
        // LCOV_DISABLED_START
        kMaxBadFormulaRepairResetSymbolicExprs};
        // LCOV_DISABLED_STOP
  };  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  for (const auto& clause : clauses) {  // LCOV_EXCL_LINE
    const StateCube badCube = cubeForbiddenByStateClause(clause);  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    if (const auto cachedCore =  // LCOV_EXCL_LINE
            findPdrResetUnreachableCoreForCube(  // LCOV_EXCL_LINE
                resetFrontierCache, badCube, targetFrame);  // LCOV_EXCL_LINE
        cachedCore.has_value()) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      learnResetConflict(*cachedCore);  // LCOV_EXCL_LINE
      ++checkedClauses;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      if (reachedDeepPartialRepairBudget()) {  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        break;  // LCOV_EXCL_LINE
      }
      continue;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }
    // LCOV_DISABLED_START
    const size_t targetStep = problem.resetBootstrapCycles + targetFrame;  // LCOV_EXCL_LINE
    if (deepResetSpecializedOnlyRepair) {  // LCOV_EXCL_LINE
      // Deep bad-formula repair is a cache consumer only. Sampling on
      // BlackParrot showed that opening fresh reset-symbolic unrolls here can
      // dominate the whole PDR run; the ordinary concrete root validator still
      // LCOV_DISABLED_STOP
      // performs exact checks and populates these caches when needed.
      // LCOV_DISABLED_START
      if (const auto priorCoreConflict =  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
              memoizedPriorResetCoreConflictAtStep(  // LCOV_EXCL_LINE
                  // LCOV_DISABLED_START
                  badCube,
                  targetFrame,  // LCOV_EXCL_LINE
                  targetStep,  // LCOV_EXCL_LINE
                  // LCOV_DISABLED_STOP
                  resetFrontierCache,  // LCOV_EXCL_LINE
                  // LCOV_DISABLED_START
                  nullptr);
          priorCoreConflict.has_value()) {  // LCOV_EXCL_LINE
        learnResetConflict(*priorCoreConflict);  // LCOV_EXCL_LINE
        ++checkedClauses;  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
        if (reachedDeepPartialRepairBudget()) {  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          break;  // LCOV_EXCL_LINE
        }
        continue;  // LCOV_EXCL_LINE
      }
      rememberResidualExactValidationCube(badCube);  // LCOV_EXCL_LINE
      ++skippedDeepResetSpecializedProbes;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
    if (reachedNonExactFreshResetProbeBudget()) {  // LCOV_EXCL_LINE
      rememberResidualExactValidationCube(badCube);  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      ++skippedDeepResetSpecializedProbes;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      continue;  // LCOV_EXCL_LINE
    }
    ++freshResetSpecializedProbes;  // LCOV_EXCL_LINE
    auto priorCoreBudget = scopedBadFormulaResetBudget();  // LCOV_EXCL_LINE
    if (const auto priorCoreConflict =  // LCOV_EXCL_LINE
            resetSpecializedPriorCoreConflictAtStep(  // LCOV_EXCL_LINE
                problem,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_STOP
                transitionByState,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                badCube,
                // LCOV_DISABLED_STOP
                targetFrame,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                targetStep,  // LCOV_EXCL_LINE
                resetFrontierCache,  // LCOV_EXCL_LINE
                nullptr,
                allowExactResetFrontierQueries);  // LCOV_EXCL_LINE
                // LCOV_DISABLED_STOP
        priorCoreConflict.has_value()) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      learnResetConflict(*priorCoreConflict);  // LCOV_EXCL_LINE
      ++learnedFreshResetConflictClauses;  // LCOV_EXCL_LINE
      ++checkedClauses;  // LCOV_EXCL_LINE
      if (reachedDeepPartialRepairBudget()) {  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      continue;  // LCOV_EXCL_LINE
    }
    if (reachedNonExactFreshResetProbeBudget()) {  // LCOV_EXCL_LINE
      rememberResidualExactValidationCube(badCube);  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      ++skippedDeepResetSpecializedProbes;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      continue;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }
    // LCOV_DISABLED_START
    ++freshResetSpecializedProbes;  // LCOV_EXCL_LINE
    auto resetConflictBudget = scopedBadFormulaResetBudget();  // LCOV_EXCL_LINE
    if (deepLocalResetSpecializedRepair) {  // LCOV_EXCL_LINE
      ++deepResetSpecializedClauseChecks;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (const auto resetConflict =  // LCOV_EXCL_LINE
            resetSpecializedConflictCubeAtStep(  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
                problem,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                transitionByState,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_STOP
                resetFrontierCache,  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                badCube,
                targetStep,  // LCOV_EXCL_LINE
                nullptr,
                allowExactResetFrontierQueries);  // LCOV_EXCL_LINE
                // LCOV_DISABLED_STOP
        resetConflict.has_value() && cubeContainsCube(badCube, *resetConflict)) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      learnResetConflict(*resetConflict);  // LCOV_EXCL_LINE
      ++learnedFreshResetConflictClauses;  // LCOV_EXCL_LINE
      ++checkedClauses;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      if (reachedDeepPartialRepairBudget()) {  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        break;  // LCOV_EXCL_LINE
      }
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_STOP
    if (reachedNonExactFreshResetProbeBudget()) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      rememberResidualExactValidationCube(badCube);  // LCOV_EXCL_LINE
      ++skippedDeepResetSpecializedProbes;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    }
    if (!allowExactResetFrontierQueries) {  // LCOV_EXCL_LINE
      rememberResidualExactValidationCube(badCube);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (cubeReachableAtConcreteFrame(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            solverType,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
            transitionByState,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            badCube,
            targetFrame,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
            resetFrontierCache,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            // This is a narrow validation of one bad assignment at the frame
            // where the new clauses will be learned. Use the shared exact
            // assumption solver and skip optional per-cube prechecks here:
            // BlackParrot sampling showed rebuilding those one-shot precheck
            // solvers dominating the validated-clause repair path.
            ConcreteCubeReachabilityMode::CachedAssumptions,
            nullptr,
            /*usePostBootstrapPrechecks=*/false)) {
            // LCOV_DISABLED_STOP
      return false;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
    ++checkedClauses;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  // Mixed repairs can learn some clauses from cheap reset-specialized checks
  // and still need a bounded exact batch for the remaining shallow cubes.
  if (allowResidualExactBatch &&  // LCOV_EXCL_LINE
      !allowExactResetFrontierQueries &&  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      !residualExactValidationOverflow &&  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      !residualExactValidationCubes.empty()) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    std::vector<std::vector<std::pair<size_t, bool>>> residualAssignments;  // LCOV_EXCL_LINE
    residualAssignments.reserve(residualExactValidationCubes.size());  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    for (const StateCube& residualCube : residualExactValidationCubes) {  // LCOV_EXCL_LINE
      residualAssignments.push_back(cubeAssignments(residualCube));  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }
    // LCOV_DISABLED_START
    auto& reachabilityContext = resetReachabilityContextFor(  // LCOV_EXCL_LINE
        resetFrontierCache, problem, transitionByState, nullptr);  // LCOV_EXCL_LINE
    const bool anyReachable =  // LCOV_EXCL_LINE
        SEC::anyStateCubeReachableAtResetFrontier(  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
            reachabilityContext,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            residualAssignments,
            targetFrame,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            kResidualResetFrontierBatchConflictLimit,
            kResidualResetFrontierBatchPropagationLimit);
    if (anyReachable) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
      return false;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
    const size_t residualChecks = residualExactValidationCubes.size();  // LCOV_EXCL_LINE
    checkedClauses += residualChecks;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    if (residualChecks != 0 && pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: batched exact residual reset-cube "
          "bad-formula checks ",
          // LCOV_DISABLED_START
          "bad_frame=", targetFrame,
          // LCOV_DISABLED_STOP
          " clauses=", residualChecks,
          " total=", clauses.size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

// LCOV_DISABLED_START

  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        allowExactResetFrontierQueries  // LCOV_EXCL_LINE
            ? "SEC PDR stats: validated bad-formula clauses with reset cubes "
            : "SEC PDR stats: partially checked bad-formula reset conflicts ",
            // LCOV_DISABLED_STOP
        "bad_frame=", targetFrame,
        // LCOV_DISABLED_START
        " clauses=", checkedClauses,
        // LCOV_DISABLED_STOP
        " total=", clauses.size(),  // LCOV_EXCL_LINE
        " deep_probes=", deepResetSpecializedClauseChecks,
        " skipped_deep_probes=", skippedDeepResetSpecializedProbes,
        " fresh_reset_probes=", freshResetSpecializedProbes,
        " learned_reset_conflicts=", learnedResetConflictClauses);
  }  // LCOV_EXCL_LINE
  if (learnedResetConflictClausesOut != nullptr) {  // LCOV_EXCL_LINE
    *learnedResetConflictClausesOut = learnedResetConflictClauses;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (checkedClauses != clauses.size()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  return true;  // LCOV_EXCL_LINE
// LCOV_DISABLED_START
}
// LCOV_DISABLED_STOP

KInductionProblem outputBadValidationProblem(
    const KInductionProblem& problem,
    const ObservedOutputBadClauseGroup& group) {
  KInductionProblem validationProblem = problem;
  validationProblem.observedOutputExprs0 = {
      problem.observedOutputExprs0[group.outputIndex]};
  // LCOV_DISABLED_START
  validationProblem.observedOutputExprs1 = {
  // LCOV_DISABLED_STOP
      problem.observedOutputExprs1[group.outputIndex]};
  validationProblem.observedOutputNames = {
      group.outputIndex < problem.observedOutputNames.size()
          ? problem.observedOutputNames[group.outputIndex]
          : std::to_string(group.outputIndex)};  // LCOV_EXCL_LINE
  validationProblem.bad = group.outputBad;
  validationProblem.property = BoolExpr::Not(group.outputBad);
  validationProblem.inductionBad = group.outputBad;
  // LCOV_DISABLED_START
  validationProblem.inductionProperty = validationProblem.property;
  return validationProblem;
}
// LCOV_DISABLED_STOP

std::optional<bool> learnPartialTargetResetFrontierBadFormulaClauses(  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant,
    const std::vector<StateClause>& clauses,
    std::vector<FrameClauses>& frames,
    size_t targetFrame,
    ResetFrontierCache& resetFrontierCache) {
    // LCOV_DISABLED_STOP
  if (problem.resetBootstrapCycles == 0 || targetFrame == 0 ||  // LCOV_EXCL_LINE
      targetFrame >= frames.size()) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  size_t cachedClauses = 0;  // LCOV_EXCL_LINE
  size_t cheapChecks = 0;  // LCOV_EXCL_LINE
  size_t learnedClauses = 0;  // LCOV_EXCL_LINE
  const size_t cheapCheckLimit =  // LCOV_EXCL_LINE
      partialTargetResetFrontierBadFormulaCheapCheckLimit(problem);  // LCOV_EXCL_LINE
  for (const auto& clause : clauses) {  // LCOV_EXCL_LINE
    if (frameHasSubsumingClause(frames[targetFrame], clause)) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    }

// LCOV_DISABLED_START

    const StateCube badCube = cubeForbiddenByStateClause(clause);  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    if (const auto cachedCore =  // LCOV_EXCL_LINE
            findPdrResetUnreachableCoreForCube(  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                resetFrontierCache, badCube, targetFrame);  // LCOV_EXCL_LINE
        cachedCore.has_value()) {  // LCOV_EXCL_LINE
      if (addClauseToFrame(frames[targetFrame], clause)) {  // LCOV_EXCL_LINE
        ++cachedClauses;  // LCOV_EXCL_LINE
        ++learnedClauses;  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
      }  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      continue;  // LCOV_EXCL_LINE
    }

    if (cheapChecks >= cheapCheckLimit) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    }

// LCOV_DISABLED_START

    ++cheapChecks;  // LCOV_EXCL_LINE
    std::optional<ScopedResetSymbolicEvaluatorBudget> scopedResetBudget;
    if (hasLargeDualRailResetFrontierSurface(problem) &&  // LCOV_EXCL_LINE
        targetFrame > kMaxResetSpecializedBadFormulaValidationFrame) {
      scopedResetBudget.emplace(  // LCOV_EXCL_LINE
          resetSymbolicEvaluatorFor(
              resetFrontierCache, problem, transitionByState),
          kMaxBadFormulaRepairResetSymbolicStates,
          kMaxBadFormulaRepairResetSymbolicExprs);
    }
    if (!cubeOutsideConcreteFrameByCheapResetFacts(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
            solverType,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            transitionByState,  // LCOV_EXCL_LINE
            badCube,
            // LCOV_DISABLED_STOP
            targetFrame,  // LCOV_EXCL_LINE
            // LCOV_DISABLED_START
            resetFrontierCache,  // LCOV_EXCL_LINE
            frameInvariant)) {  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    }

    if (addClauseToFrame(frames[targetFrame], clause)) {  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      ++learnedClauses;  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  // LCOV_DISABLED_START
  if (learnedClauses == 0) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  // LCOV_DISABLED_STOP
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: refined projected counterexample with partial "
        "target-frame reset-frontier bad-formula clauses ",
        "bad_frame=", targetFrame,
        " clauses=", learnedClauses,
        " total=", clauses.size(),  // LCOV_EXCL_LINE
        " cheap_checks=", cheapChecks,
        " cheap_limit=", cheapCheckLimit,
        " cached_clauses=", cachedClauses);
  }  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

// LCOV_DISABLED_START
std::optional<bool> learnPerOutputValidatedBadFormulaClauses(
// LCOV_DISABLED_STOP
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant,
    const std::vector<ObservedOutputBadClauseGroup>& groups,
    std::vector<FrameClauses>& frames,
    size_t targetFrame,
    size_t& badFrame,
    ResetFrontierCache& resetFrontierCache,
    bool preferWholeBadFormulaValidation = false) {
  if (problem.observedOutputExprs0.size() >
      kMaxPerOutputValidatedBadFormulaRepairOutputs) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  bool learnedAnyClause = false;
  // LCOV_DISABLED_START
  size_t checkedGroups = 0;
  size_t learnedClauses = 0;
  size_t learnedResetConflictClausesTotal = 0;
  // LCOV_DISABLED_STOP
  // Dual-rail batches can contain many independent output-local bad
  // predicates.  Once one predicate learns a reset-frontier repair, keep
  // LCOV_DISABLED_START
  // draining the current batch so PDR does not re-enter this function once per
  // output.  Binary SEC keeps the historical early-return behavior.
  const bool continueAfterLocalRepair = problem.usesDualRailStateEncoding;
  // LCOV_DISABLED_STOP
  const size_t perOutputClauseLimit =
      singleOutputBadFormulaClauseLimit(problem);
  // LCOV_DISABLED_START
  for (const auto& group : groups) {
    const bool targetFrameOnlyRepair = targetFrame > 1;
    if (group.clauses.empty()) {
      emitSkippedPerOutputBadFormulaGroupDiag(  // LCOV_EXCL_LINE
          targetFrame, group, "empty");  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
      continue;  // LCOV_EXCL_LINE
    }
    if (group.clauses.size() > perOutputClauseLimit) {
      emitSkippedPerOutputBadFormulaGroupDiag(  // LCOV_EXCL_LINE
          targetFrame, group, "clause_limit", perOutputClauseLimit);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (targetFrameOnlyRepair &&
        !hasNewValidatedBadFormulaClauseAtFrame(  // LCOV_EXCL_LINE
            frames, group.clauses, targetFrame)) {  // LCOV_EXCL_LINE
      emitSkippedPerOutputBadFormulaGroupDiag(  // LCOV_EXCL_LINE
          targetFrame, group, "target_frame_already_present");  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    if (!hasNewValidatedBadFormulaClause(frames, group.clauses, targetFrame)) {
      emitSkippedPerOutputBadFormulaGroupDiag(
          targetFrame, group, "already_present");
      continue;
    }

    ++checkedGroups;
    // The broad batch OR can be a hard SAT problem even when every individual
    // output mismatch is a tiny state-only predicate. Validate each output's
    // clauses separately, preferring the reset-cube validator because it reuses
    // the reset frontier SAT context across the whole batch.
    const KInductionProblem validationProblem =
        outputBadValidationProblem(problem, group);
    const bool useObservationFrontier =
        problem.usesResetBootstrapObservationFrontier();
    const bool allowExactResetValidation =
        !useObservationFrontier &&
        canExactlyValidateBadFormulaGroup(problem, targetFrame, group.clauses);
    bool validatedGroup = false;
    size_t learnedResetConflictClauses = 0;
    if (!useObservationFrontier) {
      if (const auto resetCubeValidation =
              validateBadFormulaClausesWithResetCubes(
                  // Reset-cube validation only asks whether the forbidden state
                  // assignments are reachable in the concrete transition system;
                  // LCOV_DISABLED_START
                  // the output-local bad formula is not part of that SAT query.
                  // Use the shared SEC problem/cache so per-output repair can
                  // LCOV_DISABLED_STOP
                  // consume exact reset cores learned by root validation.
                  // LCOV_DISABLED_START
                  problem,
                  solverType,
                  transitionByState,
                  group.clauses,
                  targetFrame,
                  // LCOV_DISABLED_STOP
                  resetFrontierCache,
                  &frames,
                  &learnedResetConflictClauses,
                  allowExactResetValidation);
          resetCubeValidation.has_value()) {
        // LCOV_DISABLED_START
        if (!*resetCubeValidation) {  // LCOV_EXCL_LINE
          return std::nullopt;  // LCOV_EXCL_LINE
        }
        // LCOV_DISABLED_STOP
        validatedGroup = true;  // LCOV_EXCL_LINE
        if (learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
          learnedAnyClause = true;  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        }  // LCOV_EXCL_LINE
        // LCOV_DISABLED_STOP
      }  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
    learnedResetConflictClausesTotal += learnedResetConflictClauses;
    bool validatedGroupAtTargetOnly = false;
    // LCOV_DISABLED_STOP
    if (!validatedGroup &&
        // LCOV_DISABLED_START
        !allowExactResetValidation &&
        // LCOV_DISABLED_STOP
        learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: refined projected counterexample with per-output "
            "partial reset-cube conflict clauses ",
            "bad_frame=", targetFrame,
            // LCOV_DISABLED_START
            " output=", group.outputIndex,  // LCOV_EXCL_LINE
            " learned_reset_conflicts=", learnedResetConflictClauses);
      }  // LCOV_EXCL_LINE
      // LCOV_DISABLED_STOP
      if (continueAfterLocalRepair) {  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        continue;  // LCOV_EXCL_LINE
      }
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_DISABLED_STOP
    if (!validatedGroup) {
      const StateCube validationSupportCube =
          // LCOV_DISABLED_START
          validationSupportCubeForStateClauses(group.clauses);
      const bool allowBatchedResetFrontierValidation =
          problem.resetBootstrapCycles != 0 &&
          !useObservationFrontier &&  // LCOV_EXCL_LINE
          targetFrame <=  // LCOV_EXCL_LINE
              (targetFrame > 1  // LCOV_EXCL_LINE
                   ? kMaxPartialTargetResetFrontierBadFormulaFrame
                   : kMaxResetFrontierBatchedBadFormulaFrame) &&  // LCOV_EXCL_LINE
          group.clauses.size() <= perOutputClauseLimit &&  // LCOV_EXCL_LINE
          !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
          validationSupportCube.size() <=  // LCOV_EXCL_LINE
              kMaxResetFrontierBatchedBadFormulaSupport;
      if (allowBatchedResetFrontierValidation) {
        const bool useTargetFrameProof = targetFrame > 1;  // LCOV_EXCL_LINE
        if (useTargetFrameProof) {  // LCOV_EXCL_LINE
          if (const auto partialTargetRepair =  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
                  learnPartialTargetResetFrontierBadFormulaClauses(  // LCOV_EXCL_LINE
                      // LCOV_DISABLED_START
                      problem,  // LCOV_EXCL_LINE
                      // LCOV_DISABLED_STOP
                      solverType,  // LCOV_EXCL_LINE
                      // LCOV_DISABLED_START
                      transitionByState,  // LCOV_EXCL_LINE
                      frameInvariant,  // LCOV_EXCL_LINE
                      group.clauses,  // LCOV_EXCL_LINE
                      frames,  // LCOV_EXCL_LINE
                      targetFrame,  // LCOV_EXCL_LINE
                      resetFrontierCache);  // LCOV_EXCL_LINE
              partialTargetRepair.has_value() && *partialTargetRepair) {  // LCOV_EXCL_LINE
            learnedAnyClause = true;  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
            if (continueAfterLocalRepair) {  // LCOV_EXCL_LINE
              // LCOV_DISABLED_START
              continue;  // LCOV_EXCL_LINE
            }
            return true;  // LCOV_EXCL_LINE
          }
        } else {  // LCOV_EXCL_LINE
          auto& reachabilityContext = resetReachabilityContextFor(  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
              resetFrontierCache, problem, transitionByState, frameInvariant);  // LCOV_EXCL_LINE
          const auto forbiddenCubes = forbiddenAssignmentCubes(group.clauses);  // LCOV_EXCL_LINE
          const bool anyReachable =  // LCOV_EXCL_LINE
              // LCOV_DISABLED_START
              SEC::anyStateCubeReachableWithinResetFrontier(  // LCOV_EXCL_LINE
                  reachabilityContext,  // LCOV_EXCL_LINE
                  solverType,  // LCOV_EXCL_LINE
                  forbiddenCubes,
                  targetFrame);  // LCOV_EXCL_LINE
          if (!anyReachable) {  // LCOV_EXCL_LINE
            validatedGroup = true;  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
            validatedGroupAtTargetOnly = false;  // LCOV_EXCL_LINE
            if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
              // LCOV_DISABLED_START
              emitSecDiag(  // LCOV_EXCL_LINE
                  "SEC PDR stats: per-output batched reset-frontier ",
                  "bad-formula proof ",
                  "bad_frame=", targetFrame,
                  " output=", group.outputIndex,  // LCOV_EXCL_LINE
                  " clauses=", group.clauses.size(),  // LCOV_EXCL_LINE
                  " support=", validationSupportCube.size());  // LCOV_EXCL_LINE
            }  // LCOV_EXCL_LINE
          }  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
        }  // LCOV_EXCL_LINE
      // LCOV_DISABLED_START
      }  // LCOV_EXCL_LINE
    }
    if (!validatedGroup && !allowExactResetValidation) {
      const size_t cachedResetValidatedAssignments =  // LCOV_EXCL_LINE
          countCachedResetValidatedBadFormulaAssignments(  // LCOV_EXCL_LINE
              group.clauses, targetFrame, resetFrontierCache);  // LCOV_EXCL_LINE
              // LCOV_DISABLED_STOP
      const bool allowWholeGroupAfterCachedRoot =  // LCOV_EXCL_LINE
          targetFrame <=  // LCOV_EXCL_LINE
              kMaxWholeBadFormulaBaseValidationAfterCachedRootFrame &&  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          group.clauses.size() <= perOutputClauseLimit &&  // LCOV_EXCL_LINE
          cachedResetValidatedAssignments != 0;  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
      if (allowWholeGroupAfterCachedRoot) {  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        const StateClauseSetKey validationKey =
            badFormulaValidationCacheKey(group.clauses, targetFrame);  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
        if (resetFrontierCache.wholeBadFormulaValidationMisses.find(  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                validationKey) ==  // LCOV_EXCL_LINE
            resetFrontierCache.wholeBadFormulaValidationMisses.end()) {  // LCOV_EXCL_LINE
          if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
            emitSecDiag(  // LCOV_EXCL_LINE
                "SEC PDR stats: trying per-output whole bad-formula "
                // LCOV_DISABLED_STOP
                "validation after cached reset roots ",
                "bad_frame=", targetFrame,
                // LCOV_DISABLED_START
                " output=", group.outputIndex,  // LCOV_EXCL_LINE
                " clauses=", group.clauses.size(),  // LCOV_EXCL_LINE
                " cached_roots=", cachedResetValidatedAssignments);
                // LCOV_DISABLED_STOP
          }  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          if (SEC::provesNoBaseCounterexampleAtFrontier(  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
                  validationProblem,
                  badFormulaValidationSolverType(solverType),  // LCOV_EXCL_LINE
                  targetFrame)) {  // LCOV_EXCL_LINE
            validatedGroup = true;  // LCOV_EXCL_LINE
          } else {  // LCOV_EXCL_LINE
            resetFrontierCache.wholeBadFormulaValidationMisses.insert(  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                validationKey);
                // LCOV_DISABLED_STOP
          }
        }  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (!validatedGroup && !allowExactResetValidation) {
      continue;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_START
    }
    // LCOV_DISABLED_STOP
    if (!validatedGroup &&
        !SEC::provesNoBaseCounterexampleAtFrontier(
            validationProblem,
            badFormulaValidationSolverType(solverType),
            targetFrame)) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    bool learnedGroupClause = false;
    for (const auto& clause : group.clauses) {
      const bool learnedClause =
          validatedGroupAtTargetOnly && targetFrame < frames.size()
              ? addClauseToFrame(frames[targetFrame], clause)  // LCOV_EXCL_LINE
              : addClauseToFrames(frames, clause, targetFrame);
      learnedAnyClause = learnedClause || learnedAnyClause;
      learnedGroupClause = learnedClause || learnedGroupClause;
      ++learnedClauses;
    }
    if (learnedGroupClause) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: refined projected counterexample with per-output "
            "validated bad-formula clauses ",
            // LCOV_DISABLED_START
            "bad_frame=", targetFrame,
            // LCOV_DISABLED_STOP
            " output=", group.outputIndex,
            " outputs=", checkedGroups,
            " clauses=", learnedClauses,
            " learned_reset_conflicts=", learnedResetConflictClausesTotal);
      }
      if (!continueAfterLocalRepair) {
        return true;
      }
    }
  }

  if (!learnedAnyClause) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: refined projected counterexample with per-output "
        "validated bad-formula clauses ",
        "bad_frame=", targetFrame,
        " outputs=", checkedGroups,
        " clauses=", learnedClauses,
        " learned_reset_conflicts=", learnedResetConflictClausesTotal);
  }  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}

std::optional<bool> learnValidatedBadFormulaClauses(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant,
    std::vector<FrameClauses>& frames,
    size_t targetFrame,
    size_t& badFrame,
    ResetFrontierCache& resetFrontierCache,
    bool preferWholeBadFormulaValidation = false) {
  ensureObservedOutputBadClauseCache(
      resetFrontierCache, problem, transitionByState.stateSymbols());
  const auto& outputBadClauseGroups =
      resetFrontierCache.observedOutputBadClauseGroups;
  const std::vector<StateClause>* badClauses =
      resetFrontierCache.observedOutputBadClauses.has_value()
          ? &*resetFrontierCache.observedOutputBadClauses
          // LCOV_DISABLED_START
          : nullptr;
          // LCOV_DISABLED_STOP
  std::optional<std::vector<StateClause>> fallbackBadClauses;
  if (badClauses == nullptr) {
    fallbackBadClauses =
        stateOnlyBadFormulaClauses(
            problem.bad,
            transitionByState.stateSymbols(),
            validatedBadFormulaCnfSupportLimit(problem));
    if (fallbackBadClauses.has_value()) {
      badClauses = &*fallbackBadClauses;
    // LCOV_DISABLED_START
    }
  }
  // LCOV_DISABLED_STOP
  if (badClauses == nullptr || badClauses->empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const bool useObservationFrontier =
      problem.usesResetBootstrapObservationFrontier();
  const size_t exactValidatedBadFormulaClauseLimit =
      problem.observedOutputExprs0.size() == 1
          // LCOV_DISABLED_START
          ? singleOutputBadFormulaClauseLimit(problem)
          // LCOV_DISABLED_STOP
          : kMaxExactValidatedBadFormulaClauses;
  const bool useWholeBatchValidation =
      preferWholeBadFormulaValidation &&
      problem.observedOutputExprs0.size() > 1 &&  // LCOV_EXCL_LINE
      badClauses->size() <= kMaxValidatedBadFormulaClauses;  // LCOV_EXCL_LINE
  if (badClauses->size() > exactValidatedBadFormulaClauseLimit &&
      !useWholeBatchValidation) {
    if (badClauses->size() <= kMaxBatchResetCubeValidatedBadFormulaClauses &&
        hasNewValidatedBadFormulaClause(frames, *badClauses, targetFrame)) {
      size_t learnedResetConflictClauses = 0;
      const bool allowBroadExactResetValidation =
          // LCOV_DISABLED_START
          canExactlyValidateBadFormulaGroup(problem, targetFrame, *badClauses);
      if (const auto resetCubeValidation =  // LCOV_EXCL_LINE
              validateBadFormulaClausesWithResetCubes(
                  problem,
                  solverType,
                  // LCOV_DISABLED_STOP
                  transitionByState,
                  // LCOV_DISABLED_START
                  *badClauses,
                  targetFrame,
                  resetFrontierCache,
                  // LCOV_DISABLED_STOP
                  &frames,
                  &learnedResetConflictClauses,
                  allowBroadExactResetValidation);
          // LCOV_DISABLED_START
          resetCubeValidation.has_value() && *resetCubeValidation) {
          // LCOV_DISABLED_STOP
        bool learnedAnyClause = false;  // LCOV_EXCL_LINE
        // LCOV_DISABLED_START
        for (const auto& clause : *badClauses) {  // LCOV_EXCL_LINE
          learnedAnyClause =  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
              addClauseToFrames(frames, clause, targetFrame) ||  // LCOV_EXCL_LINE
              // LCOV_DISABLED_START
              learnedAnyClause;  // LCOV_EXCL_LINE
              // LCOV_DISABLED_STOP
        }
        // LCOV_DISABLED_START
        if (learnedAnyClause || learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
          if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
            emitSecDiag(  // LCOV_EXCL_LINE
            // LCOV_DISABLED_STOP
                "SEC PDR stats: refined projected counterexample with "
                "batched reset-cube validated bad-formula clauses ",
                "bad_frame=", targetFrame,
                " clauses=", badClauses->size(),  // LCOV_EXCL_LINE
                // LCOV_DISABLED_START
                " learned_reset_conflicts=", learnedResetConflictClauses);
          }  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
          return true;  // LCOV_EXCL_LINE
        }
      }  // LCOV_EXCL_LINE
      if (!allowBroadExactResetValidation &&
          learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: refined projected counterexample with "
              "partial reset-cube conflict clauses ",
              "bad_frame=", targetFrame,
              " learned_reset_conflicts=", learnedResetConflictClauses);
        }  // LCOV_EXCL_LINE
        return true;  // LCOV_EXCL_LINE
      }
    }
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: skipped broad bad-formula validation ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size(),
          " limit=", exactValidatedBadFormulaClauseLimit);
    }
    return learnPerOutputValidatedBadFormulaClauses(
        problem,
        solverType,
        transitionByState,
        // LCOV_DISABLED_START
        frameInvariant,
        outputBadClauseGroups,
        // LCOV_DISABLED_STOP
        frames,
        targetFrame,
        // LCOV_DISABLED_START
        badFrame,
        resetFrontierCache);
  }
  // LCOV_DISABLED_STOP

  // Do not spend another exact bounded-prefix solve when every candidate
  // clause is already present in the target frames. AES sampling showed PDR can
  // rediscover many neighboring abstract root cubes after the first repair, and
  // LCOV_DISABLED_START
  // those duplicate validations dominated runtime while learning nothing.
  if (!hasNewValidatedBadFormulaClause(frames, *badClauses, targetFrame)) {
  // LCOV_DISABLED_STOP
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          "SEC PDR stats: validated bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());  // LCOV_EXCL_LINE
          // LCOV_DISABLED_STOP
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  // LCOV_DISABLED_START
  if (targetFrame > 1 &&
      !hasNewValidatedBadFormulaClauseAtFrame(
          frames, *badClauses, targetFrame)) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          // LCOV_DISABLED_START
          "SEC PDR stats: target bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          // LCOV_DISABLED_STOP
          " clauses=", badClauses->size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_DISABLED_START
  }

  if (frameInvariantImpliesClauses(frameInvariant, solverType, *badClauses)) {
  // LCOV_DISABLED_STOP
    bool learnedAnyClause = false;  // LCOV_EXCL_LINE
    for (const auto& clause : *badClauses) {  // LCOV_EXCL_LINE
      learnedAnyClause =  // LCOV_EXCL_LINE
          addClauseToFrames(frames, clause, targetFrame) || learnedAnyClause;  // LCOV_EXCL_LINE
    }
    if (learnedAnyClause && pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: refined projected counterexample with "
          "frame-invariant implied bad-formula clauses ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return learnedAnyClause ? std::optional<bool>{true} : std::nullopt;  // LCOV_EXCL_LINE
  }

  // Large rail-encoded frontiers make the reset-cube bad-formula repair build
  // LCOV_DISABLED_START
  // a second bounded reset solver for one leaf.  That repair is optional:
  // ordinary PDR remains sound, and the SEC strategy can leave the leaf
  // LCOV_DISABLED_STOP
  // uncovered instead of spending the workflow in this CEGAR shortcut.
  const bool largeDualRailResetFrontierSurface =
      hasLargeDualRailResetFrontierSurface(problem);
  const StateCube validationSupportCube =
      validationSupportCubeForStateClauses(*badClauses);
  const bool localDualRailResetCubeBadFormulaRepair =
      problem.usesDualRailStateEncoding &&
      problem.observedOutputExprs0.size() == 1 &&
      targetFrame <= kMaxResetSpecializedBadFormulaValidationFrame &&
      badClauses->size() <= kMaxExactResetCubeValidatedBadFormulaClauses &&
      !validationSupportCube.empty() &&
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport;
  bool validatedBadClauses = false;
  bool validatedBadClausesAtTargetOnly = false;
  // Even when the original dual-rail SEC surface is too wide for broad exact
  // reset-frontier validation, an isolated output can still expose a tiny local
  // bad predicate.  Let PDR consume cached/reset-specialized conflicts for that
  // local predicate without opening broad exact reset-frontier queries.
  if (problem.observedOutputExprs0.size() == 1 &&
      badClauses->size() > kMaxExactValidatedBadFormulaClauses &&
      !useObservationFrontier &&  // LCOV_EXCL_LINE
      ((!problem.usesDualRailStateEncoding &&
        !largeDualRailResetFrontierSurface) ||
       localDualRailResetCubeBadFormulaRepair)) {  // LCOV_EXCL_LINE
    // A one-output state-only bad predicate can still enumerate to a few dozen
    // assignments. Sampling on BlackParrot showed one broad frontier proof for
    // that whole disjunction becoming the wall, while the concrete reset-cube
    // validator can reuse reset-specific caches and check each compact bad
    // LCOV_EXCL_STOP
    // assignment directly. This is still exact: every learned clause forbids
    // one assignment that was proven unreachable at the target frame.
    // LCOV_EXCL_START
    size_t learnedResetConflictClauses = 0;  // LCOV_EXCL_LINE
    const bool allowExactResetValidation =
        !localDualRailResetCubeBadFormulaRepair;  // LCOV_EXCL_LINE
    if (const auto resetCubeValidation =  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
            validateBadFormulaClausesWithResetCubes(  // LCOV_EXCL_LINE
                // LCOV_EXCL_START
                problem,  // LCOV_EXCL_LINE
                solverType,  // LCOV_EXCL_LINE
                transitionByState,  // LCOV_EXCL_LINE
                *badClauses,  // LCOV_EXCL_LINE
                // LCOV_EXCL_STOP
                targetFrame,  // LCOV_EXCL_LINE
                resetFrontierCache,  // LCOV_EXCL_LINE
                &frames,  // LCOV_EXCL_LINE
                &learnedResetConflictClauses,
                // LCOV_EXCL_START
                allowExactResetValidation);
        resetCubeValidation.has_value()) {  // LCOV_EXCL_LINE
      if (!*resetCubeValidation) {  // LCOV_EXCL_LINE
        return std::nullopt;  // LCOV_EXCL_LINE
      }
      validatedBadClauses = true;  // LCOV_EXCL_LINE
      if (learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: refined projected counterexample with "
              "reset-cube conflict clauses ",
              "bad_frame=", targetFrame,
              // LCOV_EXCL_START
              " learned_reset_conflicts=", learnedResetConflictClauses);
        }  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (!validatedBadClauses &&  // LCOV_EXCL_LINE
        !allowExactResetValidation &&  // LCOV_EXCL_LINE
        learnedResetConflictClauses > 0) {  // LCOV_EXCL_LINE
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: refined projected counterexample with partial "
            "reset-cube conflict clauses ",
            "bad_frame=", targetFrame,
            " learned_reset_conflicts=", learnedResetConflictClauses);
      // LCOV_EXCL_START
      }  // LCOV_EXCL_LINE
      return true;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE

// LCOV_EXCL_START

  const bool allowLocalDualRailTargetFrameRepair =
      problem.usesDualRailStateEncoding &&  // LCOV_EXCL_LINE
      problem.observedOutputExprs0.size() == 1 &&
      problem.resetBootstrapCycles != 0 &&
      targetFrame > 1 &&
      targetFrame <= kMaxPartialTargetResetFrontierBadFormulaFrame &&
      badClauses->size() <= singleOutputBadFormulaClauseLimit(problem) &&  // LCOV_EXCL_LINE
      !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
      validationSupportCube.size() <= kMaxResetFrontierBatchedBadFormulaSupport;
  const bool allowBatchedResetFrontierValidation =
  // LCOV_EXCL_STOP
      !validatedBadClauses &&
      !useObservationFrontier &&
      (allowLocalDualRailTargetFrameRepair ||  // LCOV_EXCL_LINE
       (!largeDualRailResetFrontierSurface &&
        !problem.usesDualRailStateEncoding)) &&
      problem.resetBootstrapCycles != 0 && // LCOV_EXCL_LINE
      problem.observedOutputExprs0.size() == 1 && // LCOV_EXCL_LINE
      targetFrame <=  // LCOV_EXCL_LINE
          (targetFrame > 1  // LCOV_EXCL_LINE
               ? kMaxPartialTargetResetFrontierBadFormulaFrame
               : kMaxResetFrontierBatchedBadFormulaFrame) &&  // LCOV_EXCL_LINE
      badClauses->size() <= singleOutputBadFormulaClauseLimit(problem) &&  // LCOV_EXCL_LINE
      !validationSupportCube.empty() &&  // LCOV_EXCL_LINE
      validationSupportCube.size() <=  // LCOV_EXCL_LINE
          kMaxResetFrontierBatchedBadFormulaSupport;
  if (allowBatchedResetFrontierValidation) {
    const bool useTargetFrameProof = targetFrame > 1;  // LCOV_EXCL_LINE
    // LCOV_DISABLED_STOP
    if (useTargetFrameProof) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      if (const auto partialTargetRepair =  // LCOV_EXCL_LINE
              learnPartialTargetResetFrontierBadFormulaClauses(  // LCOV_EXCL_LINE
                  problem,  // LCOV_EXCL_LINE
                  solverType,  // LCOV_EXCL_LINE
                  transitionByState,  // LCOV_EXCL_LINE
                  frameInvariant,  // LCOV_EXCL_LINE
                  *badClauses,  // LCOV_EXCL_LINE
                  frames,  // LCOV_EXCL_LINE
                  // LCOV_EXCL_STOP
                  targetFrame,  // LCOV_EXCL_LINE
                  // LCOV_EXCL_START
                  resetFrontierCache);  // LCOV_EXCL_LINE
          partialTargetRepair.has_value() && *partialTargetRepair) {  // LCOV_EXCL_LINE
        return true;  // LCOV_EXCL_LINE
      }
    } else {  // LCOV_EXCL_LINE
      auto& reachabilityContext = resetReachabilityContextFor(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          resetFrontierCache, problem, transitionByState, frameInvariant);  // LCOV_EXCL_LINE
      const auto forbiddenCubes = forbiddenAssignmentCubes(*badClauses);  // LCOV_EXCL_LINE
      const bool anyReachable =  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          SEC::anyStateCubeReachableWithinResetFrontier(  // LCOV_EXCL_LINE
              reachabilityContext,  // LCOV_EXCL_LINE
              solverType,  // LCOV_EXCL_LINE
              forbiddenCubes,
              targetFrame);  // LCOV_EXCL_LINE
      if (!anyReachable) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        validatedBadClauses = true;  // LCOV_EXCL_LINE
        validatedBadClausesAtTargetOnly = false;  // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: refined projected counterexample with batched ",
              "reset-frontier bad-formula proof ",
              "bad_frame=", targetFrame,
              " clauses=", badClauses->size(),  // LCOV_EXCL_LINE
              " support=", validationSupportCube.size());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  const size_t cachedResetValidatedAssignments =
      problem.observedOutputExprs0.size() == 1
          ? countCachedResetValidatedBadFormulaAssignments(  // LCOV_EXCL_LINE
                *badClauses, targetFrame, resetFrontierCache)  // LCOV_EXCL_LINE
          : 0;
  const bool allowDeepWholeBadFormulaAfterCachedRoot =
      problem.observedOutputExprs0.size() == 1 &&
      targetFrame <=  // LCOV_EXCL_LINE
          kMaxWholeBadFormulaBaseValidationAfterCachedRootFrame &&  // LCOV_EXCL_LINE
      badClauses->size() <= singleOutputBadFormulaClauseLimit(problem) &&  // LCOV_EXCL_LINE
      cachedResetValidatedAssignments != 0;  // LCOV_EXCL_LINE
  const bool allowWholeBadFormulaBaseValidation =
      useWholeBatchValidation ||
      (!largeDualRailResetFrontierSurface &&
       targetFrame <= kMaxWholeBadFormulaBaseValidationFrame) ||
      badClauses->size() <= kMaxExactValidatedBadFormulaClauses ||
      allowDeepWholeBadFormulaAfterCachedRoot;  // LCOV_EXCL_LINE
  if (!validatedBadClauses && !allowWholeBadFormulaBaseValidation) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: skipped deep bad-formula base validation ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_STOP

  // Prove the bad formula unreachable as a whole before learning its
  // LCOV_EXCL_START
  // state-only blocking clauses when the reset-cube path is unavailable and
  // LCOV_EXCL_STOP
  // the query is still local. This is an exact CEGAR repair: the clauses are
  // learned only after the bounded base-case check proves the one-output bad
  // predicate itself is unreachable at the target frontier.
  // LCOV_EXCL_START
  if (!validatedBadClauses) {
  // LCOV_EXCL_STOP
    const StateClauseSetKey validationKey =
        // LCOV_EXCL_START
        badFormulaValidationCacheKey(*badClauses, targetFrame);
        // LCOV_EXCL_STOP
    if (allowDeepWholeBadFormulaAfterCachedRoot &&
        resetFrontierCache.wholeBadFormulaValidationMisses.find(validationKey) !=  // LCOV_EXCL_LINE
            resetFrontierCache.wholeBadFormulaValidationMisses.end()) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (allowDeepWholeBadFormulaAfterCachedRoot && pdrStatsEnabled()) {
      // LCOV_EXCL_START
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: trying deep whole bad-formula validation after "
          "cached reset roots ",
          "bad_frame=", targetFrame,
          // LCOV_EXCL_STOP
          " clauses=", badClauses->size(),  // LCOV_EXCL_LINE
          " cached_roots=", cachedResetValidatedAssignments);
    }  // LCOV_EXCL_LINE
    const bool badFormulaUnreachable =
        SEC::provesNoBaseCounterexampleAtFrontier(
            problem,
            badFormulaValidationSolverType(solverType),
            // LCOV_EXCL_START
            targetFrame);
            // LCOV_EXCL_STOP
    if (!badFormulaUnreachable) {
      // LCOV_EXCL_START
      if (allowDeepWholeBadFormulaAfterCachedRoot) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        resetFrontierCache.wholeBadFormulaValidationMisses.insert(validationKey);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  // LCOV_EXCL_START
  bool learnedAnyClause = false;
  for (const auto& clause : *badClauses) {
  // LCOV_EXCL_STOP
    learnedAnyClause =
        (validatedBadClausesAtTargetOnly && targetFrame < frames.size()
             // LCOV_EXCL_START
             ? addClauseToFrame(frames[targetFrame], clause)  // LCOV_EXCL_LINE
             : addClauseToFrames(frames, clause, targetFrame)) ||
        learnedAnyClause;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
  }
  if (!learnedAnyClause) {
    // If all validated bad-formula clauses were already present, claiming a
    // refinement would make PDR rediscover the same bad cube forever.  Let the
    // caller use the concrete root-cube refinement or report an abstract
    // counterexample for the SEC strategy to split/validate.
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: validated bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: refined projected counterexample with validated "
        "bad-formula clauses ",
        "bad_frame=", targetFrame,
        // LCOV_EXCL_START
        " clauses=", badClauses->size());
  }
  return true;
}


// LCOV_EXCL_STOP
void addStateClause(SATSolverWrapper& solver,
                    const FrameVariableStore& variables,
                    const StateClause& clause,
                    size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(clause.size());
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR frame-clause encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::to_string(frame) + " in clause of size " +  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          std::to_string(clause.size()));  // LCOV_EXCL_LINE
    }
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  solver.addClause(satClause);
}

bool clauseCoveredByVariables(const FrameVariableStore& variables,
                              const StateClause& clause) {
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  // LCOV_EXCL_START
  return true;
}

uint64_t nextClauseEmitEpoch(const FrameClauses& frameClauses) {
  if (frameClauses.clauseEmitEpochByIndex.size() !=
      frameClauses.clauses.size()) {
      // LCOV_EXCL_STOP
    frameClauses.clauseEmitEpochByIndex.assign(
        frameClauses.clauses.size(), 0);
  }
  ++frameClauses.clauseEmitEpoch;
  if (frameClauses.clauseEmitEpoch == 0) {
    // Practically unreachable, but keep the epoch scheme correct even after an
    // absurd number of local PDR queries.
    std::fill(  // LCOV_EXCL_LINE
        frameClauses.clauseEmitEpochByIndex.begin(),  // LCOV_EXCL_LINE
        frameClauses.clauseEmitEpochByIndex.end(),  // LCOV_EXCL_LINE
        0);  // LCOV_EXCL_LINE
    frameClauses.clauseEmitEpoch = 1;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return frameClauses.clauseEmitEpoch;
}

void addIndexedFrameClauses(SATSolverWrapper& solver,
                            const FrameVariableStore& variables,
                            const FrameClauses& frameClauses,
                            const std::vector<size_t>& querySymbols,
                            size_t frame) {
  // Frame clauses are filtered twice.  First use the lazy symbol index to pull
  // only clauses that touch the current SAT query.  Then keep the existing
  // variable-coverage guard because complemented partners and formula support
  // can make a symbol present without allocating every literal in a clause.
  //
  // This is intentionally an over-approximate PDR frame: omitting unrelated
  // clauses makes the predecessor query weaker, which can produce spurious
  // obligations but cannot justify an unsound blocking clause.
  ensureFrameClauseIndex(frameClauses);
  const uint64_t emitEpoch = nextClauseEmitEpoch(frameClauses);
  size_t emittedClauses = 0;
  size_t emittedLiterals = 0;
  const size_t maxProjectedFrameClauses = maxProjectedFrameClausesPerQuery();
  // LCOV_EXCL_START
  const size_t maxProjectedFrameLiterals = maxProjectedFrameLiteralsPerQuery();
  // LCOV_EXCL_STOP
  for (const auto symbol : querySymbols) {
    if (emittedClauses >= maxProjectedFrameClauses ||
        emittedLiterals >= maxProjectedFrameLiterals) {
      break;
    }
    const auto indexIt = frameClauses.clauseIndicesBySymbol.find(symbol);
    if (indexIt == frameClauses.clauseIndicesBySymbol.end()) {
      // LCOV_EXCL_START
      continue;
      // LCOV_EXCL_STOP
    }
    for (const auto clauseIndex : indexIt->second) {
      if (emittedClauses >= maxProjectedFrameClauses ||
          emittedLiterals >= maxProjectedFrameLiterals) {
        return;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      if (frameClauses.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
      // LCOV_EXCL_STOP
        continue;
      }
      frameClauses.clauseEmitEpochByIndex[clauseIndex] = emitEpoch;
      const auto& clause = frameClauses.clauses[clauseIndex];
      if (!clauseCoveredByVariables(variables, clause)) {
        continue;  // LCOV_EXCL_LINE
      }
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;  // LCOV_EXCL_LINE
      }
      if (emittedLiterals + clause.size() > maxProjectedFrameLiterals &&
          emittedClauses != 0) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      addStateClause(solver, variables, clause, frame);
      ++emittedClauses;
      emittedLiterals += clause.size();
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
}

void addAllFrameClauses(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const FrameClauses& frameClauses,
                        size_t frame) {
  // Normal projected PDR intentionally emits only cone-relevant clauses.  The
  // exact retry uses the same blocking algorithm but disables projection, so it
  // should also see the complete learned frame for its already-pruned local
  // output slice.
  for (const auto& clause : frameClauses.clauses) {
    // LCOV_EXCL_START
    if (!clauseCoveredByVariables(variables, clause)) {
      continue;  // LCOV_EXCL_LINE
    }
    addStateClause(solver, variables, clause, frame);
  }
  // LCOV_EXCL_STOP
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& literal : cube) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR cube-assumption encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " +  // LCOV_EXCL_LINE
          std::to_string(cube.size()));  // LCOV_EXCL_LINE
    }
    solver.addClause(
        // LCOV_EXCL_START
        {literal.value ? variables.getLiteral(literal.symbol, frame)
                       : -variables.getLiteral(literal.symbol, frame)});
  }
}


// LCOV_EXCL_STOP
void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(cube.size());
  for (const auto& literal : cube) {
    if (!variables.hasSymbol(literal.symbol)) {
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR negated-cube encoding missing symbol " +  // LCOV_EXCL_LINE
          std::to_string(literal.symbol) + " at frame " +  // LCOV_EXCL_LINE
          std::to_string(frame) + " in cube of size " +  // LCOV_EXCL_LINE
          std::to_string(cube.size()));  // LCOV_EXCL_LINE
    }
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.value ? -satLiteral : satLiteral);
  }
  solver.addClause(satClause);
}

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame) {
  if (problem.resetBootstrapCycles == 0) {
    return;
  }

  // PDR frames are already positioned after the concrete reset prefix. The
  // reset controls are therefore no longer free environment inputs in one-step
  // predecessor queries; they must stay at their deasserted value on every PDR
  // transition, exactly as the concrete base solver constrains them.
  for (const auto& [symbol, assertedValue] : problem.resetBootstrapInputs) {
    if (!variables.hasSymbol(symbol)) {
      continue;
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    solver.addClause(
        {assertedValue ? -variables.getLiteral(symbol, frame)
                       : variables.getLiteral(symbol, frame)});
  }
}

void addLiteralEqualityAtFrame(SATSolverWrapper& solver,
                               const FrameVariableStore& variables,
                               size_t lhsSymbol,
                               size_t rhsSymbol,
                               size_t frame) {
  if (!variables.hasSymbol(lhsSymbol) || !variables.hasSymbol(rhsSymbol)) {
    return;  // LCOV_EXCL_LINE
  }
  const int lhs = variables.getLiteral(lhsSymbol, frame);
  const int rhs = variables.getLiteral(rhsSymbol, frame);
  solver.addClause({-lhs, rhs});
  solver.addClause({lhs, -rhs});
}

bool addRelevantStructuredInitConstraints(
    const KInductionProblem& problem,
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<size_t>& querySymbols,
    size_t frame) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities =
      KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()
          ? (usesBootstrapFrontier ? problem.bootstrapStateEqualityPairs
                                   : problem.initialStateEqualityPairs)
          : emptySymbolPairs();

  std::unordered_set<size_t> querySet(querySymbols.begin(), querySymbols.end());
  bool addedConstraint = false;
  for (const auto& [symbol, value] : assignments) {
    if (querySet.find(symbol) == querySet.end() ||
        !variables.hasSymbol(symbol)) {
      continue;
    }
    solver.addClause(
        {value ? variables.getLiteral(symbol, frame)
               : -variables.getLiteral(symbol, frame)});
    addedConstraint = true;
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const bool touchesQuery =
        querySet.find(lhsSymbol) != querySet.end() ||
        querySet.find(rhsSymbol) != querySet.end();
    if (!touchesQuery) {
      continue;
    }
    addLiteralEqualityAtFrame(solver, variables, lhsSymbol, rhsSymbol, frame);
    addedConstraint = true;
  }
  return addedConstraint;
}

void addFrameConstraints(SATSolverWrapper& solver,
                         const FrameVariableStore& variables,
                         const KInductionProblem& problem,
                         BoolExpr* initFormula,
                         BoolExpr* frameInvariant,
                         const std::vector<FrameClauses>& frames,
                         size_t level,
                         size_t frame,
                         const std::vector<size_t>& querySymbols,
                         bool exactFrameClauses) {
  if (level == 0) {
    // F[0] is Init, so the SAT query is anchored directly in the startup
    // frontier rather than in learned blocking clauses.
    const bool emittedStructuredInit = addRelevantStructuredInitConstraints(
        problem, solver, variables, querySymbols, frame);
    // LCOV_EXCL_START
    if (!emittedStructuredInit && initFormula != nullptr &&
        !hasStructuredInitFacts(problem)) {
      // Observation-only startups have no per-symbol structured summary, so
      // the exact init formula must remain as the F[0] fallback. When
      // LCOV_EXCL_STOP
      // structured init facts do exist, an empty relevant subset simply means
      // the local cone is unconstrained by Init; falling back to the full
      // monolithic init formula would reintroduce unrelated symbols into a
      // reduced compact-PDR query and can make the encoder reference leaves
      // that were intentionally left out of the local solver.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      solver.addClause({encoder.encode(initFormula)});
    }
    // LCOV_DISABLED_STOP
    if (problem.resetBootstrapCycles != 0 && problem.property != nullptr) {
      // The concrete reset/bootstrap check at the start of run() proves that
      // F[0] satisfies the current SEC property slice.  Structured init
      // encoding otherwise bypasses initFormula, so encode that checked
      // property explicitly for level-0 predecessor queries.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      solver.addClause({encoder.encode(problem.property)});
    }
    // With reset-bootstrap SEC, F[0] can be a safe abstraction of the concrete
    // post-reset image. PDR may add refinement clauses here when an abstract
    // level-0 obligation is proven outside that concrete image.
    if (exactFrameClauses) {
      addAllFrameClauses(solver, variables, frames[0], frame);
    } else {
      addIndexedFrameClauses(solver, variables, frames[0], querySymbols, frame);
    }
    return;
  }

  // For higher frames, materialize the currently learned blocking clauses and
  // LCOV_EXCL_START
  // any validated strengthening invariant the strategy handed to PDR.
  if (exactFrameClauses) {
    addAllFrameClauses(solver, variables, frames[level], frame);
  } else {
  // LCOV_EXCL_STOP
    addIndexedFrameClauses(solver, variables, frames[level], querySymbols, frame);
  }
  if (frameInvariant != nullptr) {
    // The optional strengthening is treated exactly like a frame fact, but it
    // is validated before we allow the engine to rely on it.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
    solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
}

bool predecessorSourceFrameIsKnownSafe(size_t level) {
  // Predecessor queries are only issued from frames that were already checked
  // safe in an earlier PDR phase: blocking a bad cube at F[i+1] asks from F[i],
  // and propagation runs after the current frontier has been exhausted. F[0]
  // is the startup frontier and is handled separately by Init/reset facts.
  return level > 0;
}

void addSafeFramePropertyConstraint(SATSolverWrapper& solver,
                                    const FrameVariableStore& variables,
                                    const KInductionProblem& problem,
                                    size_t level,
                                    // LCOV_EXCL_START
                                    size_t frame) {
  if (!predecessorSourceFrameIsKnownSafe(level) || problem.property == nullptr) {
    return;
  }
  // LCOV_EXCL_STOP
  // Projected frame clauses intentionally omit unrelated learned clauses to
  // keep ASIC predecessor queries local. The property is the one frame fact we
  // must not let projection forget for already-safe frames; adding it is
  // logically redundant for exact PDR, but avoids fake init-reaching paths
  // that then need expensive concrete reset-frontier validation.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
  solver.addClause({encoder.encode(problem.property)});  // LCOV_EXCL_LINE
}

bool predecessorFrameClauseApplies(
    const PredecessorAssumptionSolver& cachedSolver,
    const StateClause& clause,
    bool exactFrameClauses) {
  if (!exactFrameClauses) {
    bool touchesQuery = false;
    for (const auto& literal : clause) {
      if (cachedSolver.querySymbolSet.find(literal.symbol) !=
          cachedSolver.querySymbolSet.end()) {
        touchesQuery = true;
        break;
      }
    }
    if (!touchesQuery) {
      return false; // LCOV_EXCL_LINE
    }
  }
  return clauseCoveredByVariables(*cachedSolver.variables, clause);
}

void rememberPredecessorFrameClauses(
    PredecessorAssumptionSolver& cachedSolver,
    const FrameClauses& frameClauses,
    bool exactFrameClauses) {
  for (const auto& clause : frameClauses.clauses) {
    if (predecessorFrameClauseApplies(
            cachedSolver, clause, exactFrameClauses)) {
      cachedSolver.emittedFrameClauses.insert(clause);
    }
  }
}

size_t addNewPredecessorFrameClauses(
    PredecessorAssumptionSolver& cachedSolver,
    const FrameClauses& frameClauses,
    size_t frame,
    bool exactFrameClauses) {
  size_t addedClauses = 0;
  for (const auto& clause : frameClauses.clauses) {
    if (!predecessorFrameClauseApplies(
            cachedSolver, clause, exactFrameClauses) ||
        !cachedSolver.emittedFrameClauses.insert(clause).second) {
      continue;
    }
    addStateClause(*cachedSolver.solver, *cachedSolver.variables, clause, frame);
    ++addedClauses;
  }
  return addedClauses;
}

PredecessorAssumptionSolver& getOrCreatePredecessorAssumptionSolver(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols,
    bool exactFrameClauses) {
  PredecessorAssumptionCacheKey key{
      &problem,
      &transitionByState,
      initFormula,
      frameInvariant,
      level,
      frameClausesFingerprint(frames, level),
      exactFrameClauses,
      solverSymbols};
  if (cache.solver != nullptr &&
      cache.solver->key.hasSameReusableContext(key)) {
    // PDR frames strengthen monotonically. Reuse the expensive transition and
    // frame prefix solver, then stream only newly learned frame clauses into it.
    const size_t addedClauses = addNewPredecessorFrameClauses(
        *cache.solver, frames[level], 0, exactFrameClauses);
    cache.solver->key.frameFingerprint = key.frameFingerprint;
    if (addedClauses != 0 && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor cached solver frame clauses added=",
          addedClauses,
          " level=",
          level,
          " symbols=",
          solverSymbols.size());
    }
    return *cache.solver;
  }

  auto next = std::make_unique<PredecessorAssumptionSolver>();
  next->key = std::move(key);
  next->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  next->solver->configureForSecPdrQuery(solverSymbols.size());
  next->variables =
      std::make_unique<FrameVariableStore>(*next->solver, solverSymbols, 1);
  next->querySymbolSet.insert(solverSymbols.begin(), solverSymbols.end());
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(*next->solver, *next->variables, problem, 1);
  addDualRailStateValidity(
      *next->solver, *next->variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      *next->solver,
      *next->variables,
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      0,
      solverSymbols,
      exactFrameClauses);
  addSafeFramePropertyConstraint(
      *next->solver, *next->variables, problem, level, 0);
  addPostBootstrapResetInputConstraints(
      *next->solver, *next->variables, problem, 0);
  if (level < frames.size()) {
    rememberPredecessorFrameClauses(*next, frames[level], exactFrameClauses);
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor cached solver created level=",
        level,
        " symbols=",
        solverSymbols.size(),
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " exact_frame=",
        exactFrameClauses ? 1 : 0,
        " local_leaf=",
        hasLocalDualRailFinalLeafRepairSurface(problem) ? 1 : 0);
  }
  cache.solver = std::move(next);
  return *cache.solver;
}

int64_t resourceLimitOrUnbounded(unsigned limit) {
  return limit == std::numeric_limits<unsigned>::max()
             ? -1
             : static_cast<int64_t>(limit);
}

PredecessorQueryResultKey makePredecessorQueryResultKey(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    size_t level,
    size_t frameFingerprint,
    size_t extraFrameFingerprint,
    bool exactFrameClauses,
    bool excludeTargetOnCurrentFrame,
    size_t predecessorProjectionLimit,
    const StateCube& targetCube) {
  PredecessorQueryResultKey key;
  key.problem = &problem;
  key.transitionByState = &transitionByState;
  key.initFormula = initFormula;
  key.frameInvariant = frameInvariant;
  key.level = level;
  key.frameFingerprint = frameFingerprint;
  key.extraFrameFingerprint = extraFrameFingerprint;
  key.exactFrameClauses = exactFrameClauses;
  key.excludeTargetOnCurrentFrame = excludeTargetOnCurrentFrame;
  key.predecessorProjectionLimit = predecessorProjectionLimit;
  key.targetCube = targetCube;
  return key;
}

std::optional<PredecessorQueryResultEntry> cachedPredecessorQueryResult(
    const PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& exactKey,
    const PredecessorQueryResultKey& stableUnsatKey) {
  const auto exactIt = cache.queryResults.find(exactKey);
  if (exactIt != cache.queryResults.end()) {
    return exactIt->second;
  }
  if (cache.unsatQueries.find(stableUnsatKey) != cache.unsatQueries.end()) {
    return PredecessorQueryResultEntry{}; // LCOV_EXCL_LINE
  }
  return std::nullopt;
}

PredecessorUnsatCoreCacheKey makePredecessorUnsatCoreCacheKey(
    const PredecessorQueryResultKey& key) {
  PredecessorUnsatCoreCacheKey coreKey;
  coreKey.problem = key.problem;
  coreKey.transitionByState = key.transitionByState;
  coreKey.initFormula = key.initFormula;
  coreKey.frameInvariant = key.frameInvariant;
  coreKey.level = key.level;
  coreKey.extraFrameFingerprint = key.extraFrameFingerprint;
  coreKey.exactFrameClauses = key.exactFrameClauses;
  coreKey.excludeTargetOnCurrentFrame = key.excludeTargetOnCurrentFrame;
  coreKey.predecessorProjectionLimit = key.predecessorProjectionLimit;
  return coreKey;
}

bool predecessorUnsatCoreCacheable(
    const PredecessorQueryResultKey& stableUnsatKey) {
  // Failed target-assumption cores are globally reusable only for the base
  // predecessor context. Selector assumptions for "not current target" or
  // one-off projected retry clauses can be part of the UNSAT proof, so keep
  // those answers in the exact target cache only.
  return detail::shouldSharePredecessorUnsatCore(
      stableUnsatKey.frameFingerprint,
      stableUnsatKey.extraFrameFingerprint,
      stableUnsatKey.excludeTargetOnCurrentFrame);
}

void rememberPredecessorUnsatCore(
    PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& stableUnsatKey,
    StateCube core) {
  if (!predecessorUnsatCoreCacheable(stableUnsatKey)) {
    return;
  }
  normalizeCube(core);
  if (core.empty()) {
    return; // LCOV_EXCL_LINE
  }

  auto& cores =
      cache.unsatCoresByContext[makePredecessorUnsatCoreCacheKey(stableUnsatKey)];
  for (const auto& existing : cores) {
    if (cubeContainsCube(core, existing)) {
      return;
    }
  }

  std::vector<StateCube> retained;
  retained.reserve(cores.size() + 1);
  for (auto& existing : cores) {
    if (!cubeContainsCube(existing, core)) {
      retained.push_back(std::move(existing));
    }
  }
  retained.push_back(std::move(core));
  sortStateCubesDeterministically(retained);
  if (retained.size() > kMaxPredecessorUnsatCoresPerContext) {
    retained.pop_back(); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  cores = std::move(retained);
}

std::optional<StateCube> cachedPredecessorUnsatCoreForTarget(
    const PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& stableUnsatKey,
    const StateCube& targetCube) {
  if (!predecessorUnsatCoreCacheable(stableUnsatKey)) {
    return std::nullopt;
  }
  const auto coreIt =
      cache.unsatCoresByContext.find(
          makePredecessorUnsatCoreCacheKey(stableUnsatKey));
  if (coreIt == cache.unsatCoresByContext.end()) {
    return std::nullopt;
  }
  for (const auto& core : coreIt->second) {
    if (cubeContainsCube(targetCube, core)) {
      return core;
    }
  }
  return std::nullopt;
}

void trimPredecessorQueryResultCache(PredecessorAssumptionCache& cache) {
  if (cache.queryResults.size() < kMaxPredecessorQueryResultCacheEntries &&
      cache.unsatQueries.size() < kMaxPredecessorQueryResultCacheEntries) {
    return;
  }
  // Dropping cache entries cannot change the proof; it only bounds retained
  // memory before another wave of local predecessor obligations starts.
  cache.queryResults.clear(); // LCOV_EXCL_LINE
  cache.unsatQueries.clear(); // LCOV_EXCL_LINE
  cache.unsatCoresByContext.clear(); // LCOV_EXCL_LINE
}

void rememberPredecessorQueryResult(
    PredecessorAssumptionCache& cache,
    const PredecessorQueryResultKey& exactKey,
    const PredecessorQueryResultKey& stableUnsatKey,
    const std::optional<StateCube>& predecessor,
    const StateCube* unsatCore = nullptr) {
  trimPredecessorQueryResultCache(cache);
  PredecessorQueryResultEntry entry;
  if (predecessor.has_value()) {
    entry.hasPredecessor = true;
    entry.predecessor = *predecessor;
  } else {
    if (unsatCore != nullptr && !unsatCore->empty()) {
      entry.hasUnsatCore = true;
      entry.unsatCore = *unsatCore;
      normalizeCube(entry.unsatCore);
    }
    cache.unsatQueries.insert(stableUnsatKey);
  }
  cache.queryResults.emplace(exactKey, std::move(entry));
  if (unsatCore != nullptr && !unsatCore->empty()) {
    rememberPredecessorUnsatCore(cache, stableUnsatKey, *unsatCore);
  }
}

std::optional<StateCube> cachedPredecessorUnsatCoreForCube(
    const PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t sourceLevel,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses) {
  if (sourceLevel >= frames.size()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  const auto exactKey = makePredecessorQueryResultKey(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      sourceLevel,
      frameClausesFingerprint(frames, sourceLevel),
      /*extraFrameFingerprint=*/0,
      exactFrameClauses,
      excludeTargetOnCurrentFrame,
      predecessorProjectionLimit,
      targetCube);
  const auto resultIt = cache.queryResults.find(exactKey);
  if (resultIt != cache.queryResults.end() &&
      resultIt->second.hasUnsatCore &&
      !resultIt->second.unsatCore.empty()) {
    return resultIt->second.unsatCore;
  }
  const auto stableUnsatKey = makePredecessorQueryResultKey( // LCOV_EXCL_LINE
      problem, // LCOV_EXCL_LINE
      transitionByState, // LCOV_EXCL_LINE
      initFormula, // LCOV_EXCL_LINE
      frameInvariant, // LCOV_EXCL_LINE
      sourceLevel, // LCOV_EXCL_LINE
      /*frameFingerprint=*/0,
      /*extraFrameFingerprint=*/0,
      exactFrameClauses, // LCOV_EXCL_LINE
      excludeTargetOnCurrentFrame, // LCOV_EXCL_LINE
      predecessorProjectionLimit, // LCOV_EXCL_LINE
      targetCube); // LCOV_EXCL_LINE
  return cachedPredecessorUnsatCoreForTarget( // LCOV_EXCL_LINE
      cache, stableUnsatKey, targetCube); // LCOV_EXCL_LINE
}

bool clauseTouchesQuerySymbols(const StateClause& clause,
                               const std::unordered_set<size_t>& querySymbols) {
  for (const auto& literal : clause) {
    if (querySymbols.find(literal.symbol) != querySymbols.end()) {
      return true;
    }
  }
  return false;
}

bool badCubeFrameClauseApplies(const BadCubeAssumptionSolver& cachedSolver,
                               const StateClause& clause,
                               bool exactFrameClauses) {
  if (exactFrameClauses) {
    return true;
  }
  if (!clauseTouchesQuerySymbols(clause, cachedSolver.querySymbolSet)) {
    return false;
  }
  return clauseCoveredByVariables(*cachedSolver.variables, clause);
}

void rememberBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                                 const FrameClauses& frameClauses,
                                 bool exactFrameClauses) {
  for (const auto& clause : frameClauses.clauses) {
    if (badCubeFrameClauseApplies(
            cachedSolver, clause, exactFrameClauses)) {
      cachedSolver.emittedFrameClauses.insert(clause);
    }
  }
}

void addNewBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                               const std::vector<StateClause>& frameClauses,
                               size_t beginIndex,
                               size_t frame,
                               bool exactFrameClauses,
                               const char* source) {
  size_t addedClauses = 0;
  for (size_t clauseIndex = beginIndex; clauseIndex < frameClauses.size();
       ++clauseIndex) {
    const auto& clause = frameClauses[clauseIndex];
    if (!badCubeFrameClauseApplies(cachedSolver, clause, exactFrameClauses) ||
        !cachedSolver.emittedFrameClauses.insert(clause).second) {
      continue;
    }
    // Frame vectors are compacted by subsumption, so a stronger learned clause
    // can replace a weaker one without increasing the vector size. Track by
    // clause identity instead of append index to keep cached bad-cube solvers
    // synchronized with the logical frame.
    addStateClause(*cachedSolver.solver, *cachedSolver.variables, clause, frame);
    ++addedClauses;
  }
  if (addedClauses != 0 && pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube cached frame clauses added=",
        addedClauses,
        " frame=",
        frame,
        " source=",
        source,
        " scanned=",
        frameClauses.size() - beginIndex);
  }
}

void syncBadCubeFrameClauses(BadCubeAssumptionSolver& cachedSolver,
                             const FrameClauses& frameClauses,
                             size_t frame,
                             bool exactFrameClauses,
                             size_t frameFingerprint) {
  if (cachedSolver.emittedFrameFingerprint == frameFingerprint) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: bad cube cached frame clauses unchanged frame=",
          frame,
          " fingerprint=",
          frameFingerprint);
    }
    return;
  }
  if (cachedSolver.emittedFrameLogOffset <=
      frameClauses.addedClauseLog.size()) {
    addNewBadCubeFrameClauses(
        cachedSolver,
        frameClauses.addedClauseLog,
        cachedSolver.emittedFrameLogOffset,
        frame,
        exactFrameClauses,
        "frame_log");
    cachedSolver.emittedFrameLogOffset = frameClauses.addedClauseLog.size();
  } else {
    addNewBadCubeFrameClauses( // LCOV_EXCL_LINE
        cachedSolver, // LCOV_EXCL_LINE
        frameClauses.clauses, // LCOV_EXCL_LINE
        0,
        frame, // LCOV_EXCL_LINE
        exactFrameClauses, // LCOV_EXCL_LINE
        "full_frame");
    cachedSolver.emittedFrameLogOffset = frameClauses.addedClauseLog.size(); // LCOV_EXCL_LINE
  }
  cachedSolver.emittedFrameFingerprint = frameFingerprint;
}

std::optional<SATSolverWrapper::SolveStatus>
solvePredecessorCubeWithCachedAssumptions(
    PredecessorAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& transitionSupportSymbols,
    const std::vector<size_t>& solverSymbols,
    bool excludeTargetOnCurrentFrame,
    const std::vector<StateClause>* extraFrameClauses,
    bool exactFrameClauses,
    unsigned predecessorConflictLimit,
    unsigned predecessorDecisionLimit,
    PredecessorAssumptionSolver** solvedCache = nullptr,
    std::vector<int>* solvedAssumptions = nullptr,
    StateCube* solvedUnsatCore = nullptr) {
  auto& cachedSolver = getOrCreatePredecessorAssumptionSolver(
      cache,
      problem,
      solverType,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      solverSymbols,
      exactFrameClauses);
  const auto assumptionPairs = addCachedTransitionAssumptionsForTargetCube(
      cachedSolver,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols);
  std::vector<int> assumptions = assumptionLiteralsFromPairs(assumptionPairs);
  if (excludeTargetOnCurrentFrame) {
    assumptions.push_back(
        cachedTargetExclusionAssumption(cachedSolver, targetCube, 0));
  }
  size_t extraFrameAssumptionCount = 0;
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) { // LCOV_EXCL_LINE
      if (!clauseCoveredByVariables(*cachedSolver.variables, clause)) { // LCOV_EXCL_LINE
        return std::nullopt; // LCOV_EXCL_LINE
      }
      assumptions.push_back( // LCOV_EXCL_LINE
          cachedExtraFrameClauseAssumption(cachedSolver, clause, 0)); // LCOV_EXCL_LINE
      ++extraFrameAssumptionCount; // LCOV_EXCL_LINE
    }
  } // LCOV_EXCL_LINE
  if (assumptions.empty()) {
    return std::nullopt; // LCOV_EXCL_LINE
  }

  if (solvedCache != nullptr) {
    *solvedCache = &cachedSolver;
  }
  if (solvedAssumptions != nullptr) {
    *solvedAssumptions = assumptions;
  }
  if (extraFrameAssumptionCount != 0 && pdrStatsEnabled()) {
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor cached solver extra frame assumptions=",
        extraFrameAssumptionCount,
        " level=",
        level,
        " symbols=",
        solverSymbols.size()); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  // The cached solver amortizes expensive frame/transition encoding across
  // neighboring predecessor queries. Keep both resource caps active: cached
  // assumptions are an optimization, and a hard residual leaf should fall back
  // to the fresh exact path instead of monopolizing the whole PDR run.
  const int64_t cachedPropagationLimit =
      resourceLimitOrUnbounded(predecessorDecisionLimit);
  const auto status = cachedSolver.solver->solveWithAssumptionsStatus(
      assumptions,
      resourceLimitOrUnbounded(predecessorConflictLimit),
      cachedPropagationLimit);
  if (status == SATSolverWrapper::SolveStatus::Unsat &&
      solvedUnsatCore != nullptr) {
    // Only target-cube assumptions are mapped back. Selector assumptions for
    // current-target exclusion or projected-frame retries may participate in
    // the SAT proof, but they are not state literals that can form a learned
    // PDR blocker.
    const std::vector<int> targetAssumptions =
        assumptionLiteralsFromPairs(assumptionPairs);
    *solvedUnsatCore = cachedPredecessorUnsatCoreFromTargetContext(
        *cachedSolver.solver,
        problem,
        level,
        targetCube,
        transitionSupportSymbols,
        excludeTargetOnCurrentFrame,
        extraFrameClauses,
        targetAssumptions,
        assumptionPairs);
  }
  return status;
}

BadCubeAssumptionSolver& getOrCreateBadCubeAssumptionSolver(
    BadCubeAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const std::vector<size_t>& solverSymbols,
    bool exactFrameClauses) {
  BadCubeAssumptionCacheKey key{
      &problem,
      initFormula,
      frameInvariant,
      level,
      exactFrameClauses,
      solverSymbols};
  const size_t currentFrameFingerprint =
      frameClausesFingerprint(frames, level);
  if (cache.solver != nullptr && cache.solver->key == key) {
    syncBadCubeFrameClauses(
        *cache.solver,
        frames[level],
        0,
        exactFrameClauses,
        currentFrameFingerprint);
    return *cache.solver;
  }

  auto next = std::make_unique<BadCubeAssumptionSolver>();
  next->key = std::move(key);
  next->solver = std::make_unique<SATSolverWrapper>(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  next->solver->configureForSecPdrQuery(solverSymbols.size());
  next->variables =
      std::make_unique<FrameVariableStore>(*next->solver, solverSymbols, 1);
  next->querySymbolSet.insert(solverSymbols.begin(), solverSymbols.end());
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      *next->solver, *next->variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(*next->solver, *next->variables, problem, 1);
  addDualRailStateValidity(
      *next->solver, *next->variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      *next->solver,
      *next->variables,
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      0,
      solverSymbols,
      exactFrameClauses);
  addPostBootstrapResetInputConstraints(
      *next->solver, *next->variables, problem, 0);
  next->encoder = std::make_unique<FrameFormulaEncoder>(
      *next->solver, next->variables->makeLeafLits(0));
  if (level < frames.size()) {
    rememberBadCubeFrameClauses(*next, frames[level], exactFrameClauses);
    next->emittedFrameFingerprint = currentFrameFingerprint;
    next->emittedFrameLogOffset = frames[level].addedClauseLog.size();
  }
  cache.solver = std::move(next);
  return *cache.solver;
}

int encodeCachedBadRoot(BadCubeAssumptionSolver& cachedSolver,
                        BoolExpr* badFormula) {
  const auto existing = cachedSolver.encodedBadRoots.find(badFormula);
  if (existing != cachedSolver.encodedBadRoots.end()) {
    return existing->second;
  }
  const int root = cachedSolver.encoder->encode(badFormula);
  cachedSolver.encodedBadRoots.emplace(badFormula, root);
  return root;
}

SATSolverWrapper::SolveStatus solveBadCubeWithCachedAssumption(
    BadCubeAssumptionCache& cache,
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    BoolExpr* badFormula,
    const std::vector<size_t>& solverSymbols,
    bool exactFrameClauses,
    unsigned badCubeConflictLimit,
    BadCubeAssumptionSolver** solvedCache) {
  auto& cachedSolver = getOrCreateBadCubeAssumptionSolver(
      cache,
      problem,
      solverType,
      initFormula,
      frameInvariant,
      frames,
      level,
      solverSymbols,
      exactFrameClauses);
  const int badRoot = encodeCachedBadRoot(cachedSolver, badFormula);
  *solvedCache = &cachedSolver;
  // The cached solver keeps learned clauses across monotonic frame updates.
  // Keep the conflict cap for workflow safety, but do not cap decisions here:
  // on wide dual-rail datapaths CaDiCaL otherwise returns UNKNOWN before those
  // learned clauses can pay back the reused frame context.
  return cachedSolver.solver->solveWithAssumptionsStatus(
      {badRoot},
      resourceLimitOrUnbounded(badCubeConflictLimit),
      /*propagationLimit=*/-1);
} // LCOV_EXCL_LINE

StateCube extractStateCube(const SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const std::vector<size_t>& stateSymbols,
                           size_t frame) {
  StateCube cube;
  cube.reserve(stateSymbols.size());
  for (const auto symbol : stateSymbols) {
    cube.push_back({symbol, solver.getLiteralValue(variables.getLiteral(symbol, frame))});
  }
  normalizeCube(cube);
  return cube;
}

void addComplementedPartnerAssignments(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const ComplementPartnerIndex& complementPartners,
    size_t frame,
    std::unordered_map<size_t, bool>& assignments) {
  // Predecessor projection cubes are intentionally tiny, while ASIC SEC
  // designs can have thousands of complemented flop pairs. Walk only the
  // partners of symbols already present in the cube instead of rescanning the
  // whole pair table for every SAT predecessor query.
  // LCOV_EXCL_START
  std::vector<size_t> worklist;
  worklist.reserve(assignments.size());
  // LCOV_EXCL_STOP
  for (const auto& [symbol, value] : assignments) {
    // LCOV_EXCL_START
    (void)value;
    worklist.push_back(symbol);
  }
  std::sort(worklist.begin(), worklist.end());

  // LCOV_EXCL_STOP
  for (size_t index = 0; index < worklist.size(); ++index) {
    // LCOV_EXCL_START
    const size_t symbol = worklist[index];
    const auto partnersIt = complementPartners.partnersBySymbol.find(symbol);
    if (partnersIt == complementPartners.partnersBySymbol.end()) {
    // LCOV_EXCL_STOP
      continue;
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    if (!variables.hasSymbol(symbol)) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    for (const auto partnerSymbol : partnersIt->second) {  // LCOV_EXCL_LINE
      if (assignments.find(partnerSymbol) != assignments.end() ||  // LCOV_EXCL_LINE
          !variables.hasSymbol(partnerSymbol)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      assignments[partnerSymbol] =  // LCOV_EXCL_LINE
          solver.getLiteralValue(variables.getLiteral(partnerSymbol, frame));  // LCOV_EXCL_LINE
      worklist.push_back(partnerSymbol);  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
}

bool formulaModelValue(const SATSolverWrapper& solver,
                       const std::unordered_map<size_t, int>& leafLits,
                       // LCOV_EXCL_START
                       BoolExpr* formula,
                       // LCOV_EXCL_STOP
                       std::unordered_map<BoolExpr*, bool>& memo) {
  // LCOV_EXCL_START
  if (formula == nullptr) {
    return false;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  if (const auto it = memo.find(formula); it != memo.end()) {
    return it->second;
  }

// LCOV_EXCL_START

  bool value = false;
  switch (formula->getOp()) {
  // LCOV_EXCL_STOP
    case Op::VAR:
      // LCOV_EXCL_START
      if (formula->getId() == 0) {
        value = false;  // LCOV_EXCL_LINE
      } else if (formula->getId() == 1) {
        value = true;  // LCOV_EXCL_LINE
      } else {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        value = solver.getLiteralValue(leafLits.at(formula->getId()));
      // LCOV_EXCL_START
      }
      break;
    case Op::NOT:
      value = !formulaModelValue(  // LCOV_EXCL_LINE
          solver, leafLits, formula->getLeft(), memo);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      break;  // LCOV_EXCL_LINE
    case Op::AND:
      value = formulaModelValue(  // LCOV_EXCL_LINE
                  solver, leafLits, formula->getLeft(), memo) &&  // LCOV_EXCL_LINE
              formulaModelValue(  // LCOV_EXCL_LINE
                  solver, leafLits, formula->getRight(), memo);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      break;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    case Op::OR:
      // LCOV_EXCL_START
      value = formulaModelValue(  // LCOV_EXCL_LINE
                  solver, leafLits, formula->getLeft(), memo) ||  // LCOV_EXCL_LINE
                  // LCOV_EXCL_STOP
              formulaModelValue(  // LCOV_EXCL_LINE
                  solver, leafLits, formula->getRight(), memo);  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
    case Op::XOR:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) ^
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::NONE:  // LCOV_EXCL_LINE
    default:
      value = false;  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
  }
  memo.emplace(formula, value);
  // LCOV_EXCL_START
  return value;
  // LCOV_EXCL_STOP
}

void addJustifyingStateLiterals(
    const SATSolverWrapper& solver,
    const std::unordered_map<size_t, int>& leafLits,
    BoolExpr* formula,
    bool desiredValue,
    const std::unordered_set<size_t>& stateSymbols,
    std::unordered_map<BoolExpr*, bool>& valueMemo,
    std::unordered_map<size_t, bool>& assignments,
    JustificationBudget* budget = nullptr) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  if (budget != nullptr) {
    if (budget->exhausted ||
        budget->remainingVisits == 0 ||
        assignments.size() >= budget->maxAssignments) {
      budget->exhausted = true;
      return;
    }
    --budget->remainingVisits;
  }

  switch (formula->getOp()) {
    case Op::VAR:
      if (stateSymbols.find(formula->getId()) != stateSymbols.end()) {
        assignments[formula->getId()] = desiredValue;
        if (budget != nullptr && assignments.size() >= budget->maxAssignments) {
          budget->exhausted = true;
        }
      }
      return;
    case Op::NOT:
      addJustifyingStateLiterals(
          solver,
          leafLits,
          formula->getLeft(),
          !desiredValue,
          stateSymbols,
          // LCOV_EXCL_START
          valueMemo,
          assignments,
          budget);
      return;
    case Op::AND:
      if (desiredValue) {
      // LCOV_EXCL_STOP
        addJustifyingStateLiterals(
            // LCOV_EXCL_START
            solver, leafLits, formula->getLeft(), true,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), true,
            // LCOV_EXCL_STOP
            stateSymbols, valueMemo, assignments, budget);
      } else {
        const bool leftValue = formulaModelValue(  // LCOV_EXCL_LINE
            solver, leafLits, formula->getLeft(), valueMemo);  // LCOV_EXCL_LINE
        addJustifyingStateLiterals(  // LCOV_EXCL_LINE
            solver,  // LCOV_EXCL_LINE
            leafLits,  // LCOV_EXCL_LINE
            leftValue ? formula->getRight() : formula->getLeft(),  // LCOV_EXCL_LINE
            false,
            stateSymbols,  // LCOV_EXCL_LINE
            valueMemo,  // LCOV_EXCL_LINE
            assignments,  // LCOV_EXCL_LINE
            budget);  // LCOV_EXCL_LINE
      }
      return;
    case Op::OR:
      // LCOV_EXCL_START
      if (desiredValue) {
        const bool leftValue = formulaModelValue(
            solver, leafLits, formula->getLeft(), valueMemo);
        addJustifyingStateLiterals(
            solver,
            leafLits,
            // LCOV_EXCL_STOP
            leftValue ? formula->getLeft() : formula->getRight(),
            true,
            stateSymbols,
            valueMemo,
            assignments,
            budget);
      } else {
        addJustifyingStateLiterals(  // LCOV_EXCL_LINE
            solver, leafLits, formula->getLeft(), false,  // LCOV_EXCL_LINE
            stateSymbols, valueMemo, assignments, budget);  // LCOV_EXCL_LINE
        addJustifyingStateLiterals(  // LCOV_EXCL_LINE
            solver, leafLits, formula->getRight(), false,  // LCOV_EXCL_LINE
            stateSymbols, valueMemo, assignments, budget);  // LCOV_EXCL_LINE
      }
      return;
    case Op::XOR: {
      const bool leftValue = formulaModelValue(
          // LCOV_EXCL_START
          solver, leafLits, formula->getLeft(), valueMemo);
          // LCOV_EXCL_STOP
      const bool rightValue = formulaModelValue(
          // LCOV_EXCL_START
          solver, leafLits, formula->getRight(), valueMemo);
          // LCOV_EXCL_STOP
      if ((leftValue ^ rightValue) == desiredValue) {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), leftValue,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), rightValue,
            stateSymbols, valueMemo, assignments, budget);
      }
      return;
    }
    case Op::NONE:  // LCOV_EXCL_LINE
    default:
      return;  // LCOV_EXCL_LINE
  }
}

StateCube extractBadJustificationCube(const SATSolverWrapper& solver,
                                      const FrameVariableStore& variables,
                                      BoolExpr* badFormula,
                                      const std::unordered_set<size_t>& stateSymbols,
                                      size_t maxAssignments,
                                      size_t frame) {
  std::unordered_map<BoolExpr*, bool> valueMemo;
  std::unordered_map<size_t, bool> assignments;
  const auto leafLits = variables.makeLeafLits(frame);
  JustificationBudget budget{
      std::max(
          kMinPredecessorJustificationVisits,
          maxAssignments * kPredecessorJustificationVisitMultiplier),
      maxAssignments,
      false};
  addJustifyingStateLiterals(
      solver,
      leafLits,
      badFormula,
      true,
      stateSymbols,
      valueMemo,
      assignments,
      maxAssignments == 0 ? nullptr : &budget);

  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

StateCube extractPredecessorJustificationCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    const std::unordered_map<size_t, int>& transitionLeafLits,
    const ComplementPartnerIndex& complementPartners,
    size_t maxAssignments,
    size_t frame) {
  std::unordered_map<BoolExpr*, bool> valueMemo;
  std::unordered_map<size_t, bool> assignments;
  // This projection is a CEGAR-style obligation reduction. It is allowed to
  // return a subset of the satisfying predecessor model because every learned
  // clause is still guarded by a real predecessor query, and any reported
  // counterexample is concrete-BMC validated by the top SEC strategy.
  // LCOV_EXCL_START
  JustificationBudget budget{
      std::max(
          kMinPredecessorJustificationVisits,
          maxAssignments * kPredecessorJustificationVisitMultiplier),
          // LCOV_EXCL_STOP
      maxAssignments,
      false};
  const auto& stateSymbols = transitionByState.stateSymbols();
  const auto& primaryByComplement = transitionByState.primaryByComplement();

// LCOV_EXCL_START

  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    // LCOV_EXCL_STOP
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);  // LCOV_EXCL_LINE
      if (primaryIt == primaryByComplement.end() ||  // LCOV_EXCL_LINE
          !transitionByState.contains(primaryIt->second)) {  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      // The target names a complemented flop output. The transition relation
      // is encoded on the primary flop, and addComplementedStateRelations()
      // constrains the complemented next-state literal to be its inverse.
      transitionSymbol = primaryIt->second;  // LCOV_EXCL_LINE
      desiredValue = !desiredValue;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE

    addJustifyingStateLiterals(
        solver,
        transitionLeafLits,
        transitionByState.at(transitionSymbol),
        desiredValue,
        stateSymbols,
        valueMemo,
        assignments,
        &budget);
    if (budget.exhausted) {
      break;
    }
  }

  addComplementedPartnerAssignments(
      solver, variables, complementPartners, frame, assignments);

  StateCube cube;
  cube.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    cube.push_back({symbol, value});
  }
  normalizeCube(cube);
  return cube;
}

StateCube extractSolvedPredecessorCube(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    const std::vector<size_t>& predecessorSymbols,
    const std::unordered_map<size_t, int>& transitionLeafLits,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit) {
  // Keep the carried obligation compact, including level-0 reset-bootstrap
  // predecessors. The predecessor SAT query remains exact for the requested
  // target, learned clauses are still validated by UNSAT predecessor or exact
  // reset-frontier checks, and reported counterexamples are validated against
  // the original root cube by the bounded concrete prefix path below. Carrying
  // the full level-0 support was measured on BlackParrot to turn one concrete
  // reset-precheck into hundreds of 600-bit reset-frontier refinement queries.
  if (predecessorProjectionLimit != 0 &&
      predecessorSymbols.size() > predecessorProjectionLimit) {
    const StateCube projectedCube = extractPredecessorJustificationCube(
        solver,
        variables,
        problem,
        transitionByState,
        targetCube,
        transitionLeafLits,
        complementPartners,
        predecessorProjectionLimit,
        0);
    if (!projectedCube.empty()) {
      return boundedPrefixCube(projectedCube, predecessorProjectionLimit);
    }
    // Some transition encodings can be satisfied without a compact structural
    // justification path. Falling back to the full SAT model can create
    // thousands of predecessor literals and make reset-bootstrap PDR enumerate
    // huge abstract cubes. Keep the CEGAR contract instead: carry a bounded
    // subset of the satisfying predecessor model, then rely on later exact
    // predecessor checks and concrete BMC validation before accepting any
    // result.
    const std::vector<size_t> boundedSymbols =
        boundedPrefixSymbols(predecessorSymbols, predecessorProjectionLimit);
    return extractStateCube(solver, variables, boundedSymbols, 0);
  }

  // Keep smaller predecessor obligations as concrete state assignments over
  // the target transition cone.  For large cones, including level-0 cubes, the
  // structural projection above prevents one SAT model from turning hundreds of
  // unrelated support flops into the next target.
  return boundedPrefixCube(
      extractStateCube(solver, variables, predecessorSymbols, 0),
      predecessorProjectionLimit);
}

StateCube extractSolvedBadCubeForFormula(
    const SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    BoolExpr* badFormula,
    const std::optional<std::vector<size_t>>& preciseBadStateSupport,
    size_t structuralBadProjectionLimit,
    const std::unordered_set<size_t>& stateSymbols,
    size_t level) {
  // Start with the full state support when it is bounded. That gives PDR a
  // precise bad obligation instead of a tiny projection that can mix unrelated
  // state valuations and later look like a counterexample only in the abstract.
  if (preciseBadStateSupport.has_value() && !preciseBadStateSupport->empty()) {
    if (isSecDiagEnabled()) {
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: PDR bad cube uses precise state support: ",
          preciseBadStateSupport->size(),  // LCOV_EXCL_LINE
          " state symbols at F",
          level);
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    StateCube cube = boundedPrefixCube(
    // LCOV_EXCL_STOP
        extractStateCube(solver, variables, *preciseBadStateSupport, 0),
        structuralBadProjectionLimit);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          // LCOV_EXCL_START
          "SEC PDR stats: bad cube level=", level,
          // LCOV_EXCL_STOP
          " source=precise support=", preciseBadStateSupport->size(),
          " cube=", cube.size(),
          " hash=", cubeFingerprint(cube),
          " limit=", structuralBadProjectionLimit);
    }
    return cube;
  }

  if (isSecDiagEnabled()) {
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC diag: PDR bad cube falls back to structural justification at F",
        level,
        " after support budget ",
        kMaxPreciseBadCubeSupportNodes);
  }  // LCOV_EXCL_LINE

  // Very large ASIC datapaths still need a compact fallback: extracting every
  // state bit in the bad cone would force every later predecessor query to
  // encode the transition for all of those latches. The structural
  // justification keeps one satisfying branch of OR/AND style bad formulas.
  StateCube cube = boundedPrefixCube(
      extractBadJustificationCube(
          solver,
          variables,
          badFormula,
          stateSymbols,
          structuralBadProjectionLimit,
          0),
      structuralBadProjectionLimit);
  const char* source = "structural";
  if (cube.empty() && structuralBadProjectionLimit != 0) {
    // A satisfying bad formula may be justified by input-only logic while the
    // bad cone still contains state. Carry a small model slice instead of the
    // vacuous empty cube, which otherwise makes PDR validate "all states" as an
    // abstract counterexample and hides useful frame learning.
    const std::vector<size_t> fallbackSymbols =
        collectStateSupportPrefixSymbols(
            badFormula,
            kMaxPreciseBadCubeSupportNodes,
            structuralBadProjectionLimit,
            stateSymbols);
    if (!fallbackSymbols.empty()) {
      cube = extractStateCube(solver, variables, fallbackSymbols, 0);
      source = "structural_model_fallback";
    }
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube level=", level,
        " source=", source,
        " cube=", cube.size(),
        " hash=", cubeFingerprint(cube),
        " limit=", structuralBadProjectionLimit);
  }
  return cube;
}

std::optional<StateCube> findBadCubeForFormula(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    BoolExpr* badFormula,
    const std::optional<std::vector<size_t>>& preciseBadStateSupport,
    size_t structuralBadProjectionLimit,
    const std::unordered_set<size_t>& stateSymbols,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    bool exactFrameClauses,
    BadCubeAssumptionCache* badCubeAssumptionCache,
    PdrFormulaSupportCache* supportCache) {
  // Search the current frame for a concrete state that still satisfies bad
  // after all learned blocking clauses and optional strengthening are applied.
  const std::vector<size_t> solverSymbols =
      findBadQuerySymbols(
          problem,
          initFormula,
          frameInvariant,
          frames,
          badFormula,
          level,
          complementPartners,
          exactFrameClauses,
          supportCache);
  const unsigned badCubeConflictLimit =
      // LCOV_EXCL_START
      problem.usesDualRailStateEncoding ? dualRailBadCubeConflictLimit() : 0;
      // LCOV_EXCL_STOP
  if (problem.usesDualRailStateEncoding && badCubeAssumptionCache != nullptr) {
    BadCubeAssumptionSolver* solvedCache = nullptr;
    const auto badSolveStatus = solveBadCubeWithCachedAssumption(
        *badCubeAssumptionCache,
        problem,
        solverType,
        initFormula,
        frameInvariant,
        frames,
        level,
        badFormula,
        solverSymbols,
        exactFrameClauses,
        badCubeConflictLimit,
        &solvedCache);
    if (badSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: bad cube query budget exhausted limit=",
            badCubeConflictLimit,
            " symbols=",
            solverSymbols.size(),  // LCOV_EXCL_LINE
            " level=",
            level,
            " cached_assumptions=1");
      }  // LCOV_EXCL_LINE
      markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (badSolveStatus == SATSolverWrapper::SolveStatus::Unsat) {
      return std::nullopt;
    }
    return extractSolvedBadCubeForFormula(
        *solvedCache->solver,
        *solvedCache->variables,
        badFormula,
        preciseBadStateSupport,
        structuralBadProjectionLimit,
        stateSymbols,
        level);
  }

  SATSolverWrapper solver(solverType);
  // Bad-state queries are local PDR obligations and are rebuilt repeatedly as
  // frames advance. Keep them on the PDR-local profile: small regressions such
  // as GCD can otherwise spend minutes in Kissat's speculative
  // preprocessing/probing before the actual frame query starts.
  // LCOV_EXCL_START
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  // LCOV_EXCL_STOP
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols, exactFrameClauses);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(badFormula)});
  SATSolverWrapper::SolveStatus badSolveStatus =
      SATSolverWrapper::SolveStatus::Sat;
  if (badCubeConflictLimit != 0) {
    // Dual-rail residual repairs can be SAT and decision-heavy even when they
    // do not accumulate many conflicts. Bound both resources so a single
    // LCOV_EXCL_START
    // uncovered output cannot dominate the whole workflow.
    // LCOV_EXCL_STOP
    badSolveStatus = solver.solveWithResourceLimits( // LCOV_EXCL_LINE
        badCubeConflictLimit, // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        /*decisionLimit=*/badCubeConflictLimit);
        // LCOV_EXCL_STOP
  } else { // LCOV_EXCL_LINE
    badSolveStatus = solver.solveStatus();
  }
  if (badSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: bad cube query budget exhausted limit=",
          badCubeConflictLimit,
          " symbols=",
          solverSymbols.size(),  // LCOV_EXCL_LINE
          " level=",
          level);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (badSolveStatus == SATSolverWrapper::SolveStatus::Unsat) {
    return std::nullopt;
  }

  return extractSolvedBadCubeForFormula(
      solver,
      variables,
      badFormula,
      preciseBadStateSupport,
      structuralBadProjectionLimit,
      stateSymbols,
      level);
}

std::optional<StateCube> findBadCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     BoolExpr* frameInvariant,
                                     const std::vector<FrameClauses>& frames,
                                     const std::optional<std::vector<size_t>>&
                                         preciseBadStateSupport,
                                     size_t preciseBadCubeStateLimit,
                                     const std::unordered_set<size_t>& stateSymbols,
                                     size_t level,
                                     const ComplementPartnerIndex& complementPartners,
                                     bool exactFrameClauses,
                                     BadCubeAssumptionCache* badCubeAssumptionCache,
                                     PdrFormulaSupportCache* supportCache) {
  if (problem.observedOutputExprs0.size() <= 1 ||
      problem.observedOutputExprs0.size() != problem.observedOutputExprs1.size()) {
    return findBadCubeForFormula(
        problem,
        solverType,
        initFormula,
        frameInvariant,
        frames,
        problem.bad,
        preciseBadStateSupport,
        preciseBadCubeStateLimit,
        stateSymbols,
        level,
        complementPartners,
        exactFrameClauses,
        badCubeAssumptionCache,
        supportCache);
  }

  // The batch bad predicate is an OR over output mismatches. Asking SAT for the
  // whole OR is logically compact, but it can be a poor search problem on ASIC
  // SEC because the solver first has to reason across unrelated output cones.
  // Query each output mismatch independently: if any bit can be bad, PDR gets
  // a real bad cube; if every bit is UNSAT, the batched bad OR is UNSAT too.
  for (size_t output = 0; output < problem.observedOutputExprs0.size(); ++output) {
    BoolExpr* outputBad = BoolExpr::simplify(
        BoolExpr::Xor(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
    const auto outputStateSupport = collectBoundedStateSupportSymbols(
        outputBad,
        kMaxPreciseBadCubeSupportNodes,
        preciseBadCubeStateLimit,
        stateSymbols);
    if (auto cube = findBadCubeForFormula(
            problem,
            solverType,
            initFormula,
            frameInvariant,
            frames,
            outputBad,
            outputStateSupport,
            preciseBadCubeStateLimit,
            stateSymbols,
            level,
            complementPartners,
            exactFrameClauses,
            badCubeAssumptionCache,
            supportCache);
        cube.has_value()) {
      return cube;
    }
    if (hasPdrBudgetExhaustion()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }
  return std::nullopt;
}

std::optional<bool> proveLargeDualRailPredecessorWithResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant,
    size_t level,
    const StateCube& targetCube,
    const std::vector<size_t>& transitionSupportSymbols,
    bool exactResetFrontierChecksEnabled,
    size_t exactResetPrecheckSupportLimit,
    ResetFrontierCache* resetFrontierCache,
    const char* phase) {
  if (resetFrontierCache == nullptr ||
      problem.resetBootstrapCycles == 0 ||
      !detail::shouldRetryLargeDualRailPredecessorWithResetFrontier( // LCOV_EXCL_LINE
          problem.usesDualRailStateEncoding, // LCOV_EXCL_LINE
          exactResetFrontierChecksEnabled, // LCOV_EXCL_LINE
          problem.observedOutputExprs0.size(), // LCOV_EXCL_LINE
          level, // LCOV_EXCL_LINE
          targetCube.size(), // LCOV_EXCL_LINE
          transitionSupportSymbols.size(), // LCOV_EXCL_LINE
          exactResetPrecheckSupportLimit)) { // LCOV_EXCL_LINE
    return std::nullopt;
  }

  const bool outsideConcreteResetFrontier = // LCOV_EXCL_LINE
      cubeOutsideConcreteResetFrontier( // LCOV_EXCL_LINE
          problem, // LCOV_EXCL_LINE
          solverType, // LCOV_EXCL_LINE
          transitionByState, // LCOV_EXCL_LINE
          targetCube, // LCOV_EXCL_LINE
          /*postBootstrapSteps=*/1,
          *resetFrontierCache, // LCOV_EXCL_LINE
          /*useResetConstantShortcut=*/false,
          ConcreteCubeReachabilityMode::CachedAssumptions,
          frameInvariant, // LCOV_EXCL_LINE
          /*resourceLimitStartupExactQuery=*/false);
  if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor reset-frontier ",
        phase,
        " ",
        "level=", level,
        " target_cube=", targetCube.size(), // LCOV_EXCL_LINE
        " target_hash=", cubeFingerprint(targetCube), // LCOV_EXCL_LINE
        " transition_support=", transitionSupportSymbols.size(), // LCOV_EXCL_LINE
        " result=", outsideConcreteResetFrontier ? "unsat" : "not_proved"); // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE
  return outsideConcreteResetFrontier; // LCOV_EXCL_LINE
}

std::optional<StateCube> findPredecessorCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const StateCube& targetCube,
    bool excludeTargetOnCurrentFrame,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses,
    ResetFrontierCache* resetFrontierCache = nullptr,
    PredecessorAssumptionCache* predecessorAssumptionCache = nullptr,
    const std::vector<StateClause>* extraFrameClauses = nullptr,
    size_t* predecessorQueryBudget = nullptr,
    bool useExactResetFrontierChecks = true,
    PdrFormulaSupportCache* supportCache = nullptr) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  std::optional<PredecessorQueryResultKey> exactCacheKey;
  std::optional<PredecessorQueryResultKey> stableUnsatCacheKey;
  const bool usePredecessorQueryResultCache =
      predecessorAssumptionCache != nullptr &&
      canUsePredecessorQueryResultCache(problem);
  if (usePredecessorQueryResultCache) {
    const size_t frameFingerprint = frameClausesFingerprint(frames, level);
    const size_t extraFrameFingerprint =
        extraFrameClausesFingerprint(extraFrameClauses);
    exactCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        frameFingerprint,
        extraFrameFingerprint,
        exactFrameClauses,
        excludeTargetOnCurrentFrame,
        predecessorProjectionLimit,
        targetCube);
    stableUnsatCacheKey = makePredecessorQueryResultKey(
        problem,
        transitionByState,
        initFormula,
        frameInvariant,
        level,
        /*frameFingerprint=*/0,
        extraFrameFingerprint,
        exactFrameClauses,
        excludeTargetOnCurrentFrame,
        predecessorProjectionLimit,
        targetCube);
    if (const auto cached = cachedPredecessorQueryResult(
            *predecessorAssumptionCache, *exactCacheKey,
            *stableUnsatCacheKey);
        cached.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor result cache hit level=",
            level,
            " extra_frame_fingerprint=",
            extraFrameFingerprint,
            " has_predecessor=",
            cached->hasPredecessor ? 1 : 0);
      }
      if (cached->hasPredecessor) {
        return cached->predecessor;
      }
      return std::nullopt; // LCOV_EXCL_LINE
    }
    if (const auto cachedCore = cachedPredecessorUnsatCoreForTarget(
            *predecessorAssumptionCache, *stableUnsatCacheKey, targetCube);
        cachedCore.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor unsat-core cache hit level=",
            level,
            " target_cube=",
            targetCube.size(),
            " core_cube=",
            cachedCore->size(),
            " target_hash=",
            cubeFingerprint(targetCube),
            " core_hash=",
            cubeFingerprint(*cachedCore));
      }
      rememberPredecessorQueryResult(
          *predecessorAssumptionCache,
          *exactCacheKey,
          *stableUnsatCacheKey,
          std::nullopt,
          &*cachedCore);
      return std::nullopt;
    }
  }
  if (!consumePdrPredecessorQueryBudget(predecessorQueryBudget)) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  PredecessorTargetSurface uncachedTargetSurface;
  const PredecessorTargetSurface* targetSurface = nullptr;
  if (predecessorAssumptionCache != nullptr) {
    targetSurface = &predecessorTargetSurfaceFor(
        *predecessorAssumptionCache, problem, transitionByState, targetCube);
  } else {
    uncachedTargetSurface = // LCOV_EXCL_LINE
        buildPredecessorTargetSurface(problem, transitionByState, targetCube); // LCOV_EXCL_LINE
    targetSurface = &uncachedTargetSurface; // LCOV_EXCL_LINE
  }
  const std::vector<size_t>& encodedTargets =
      targetSurface->encodedTargets;
  const std::vector<size_t>& transitionSupportSymbols =
      targetSurface->transitionSupportSymbols;
  const size_t transitionEncodingNodes =
      targetSurface->transitionEncodingNodes;
  const size_t statsQueryNumber = nextPdrPredecessorQueryNumber();
  const bool emitStatsForQuery = shouldEmitPdrStats(statsQueryNumber);
  // LCOV_EXCL_START
  const bool predecessorQueryIsAlreadyExact = predecessorProjectionLimit == 0;
  // LCOV_EXCL_STOP
  const size_t exactResetPrecheckSupportLimit =
      maxExactResetPrecheckTransitionSupport(solverType);
  const size_t localExactResetPrecheckSupportLimit =
      detail::effectiveLocalDualRailExactResetPrecheckSupportLimit(
          hasLocalDualRailFinalLeafRepairSurface(problem),
          problem.observedOutputExprs0.size(),
          level,
          targetCube.size(),
          exactResetPrecheckSupportLimit,
          kMinLocalDualRailFinalLeafPredecessorSupport);
  if (problem.usesDualRailStateEncoding) {
    const size_t encodingNodeLimit = dualRailPredecessorEncodingNodeLimit();
    const size_t configuredEncodingSupportLimit =
        dualRailPredecessorEncodingSupportLimit();
    // Isolated Swerv leaves measured predecessor supports slightly above the
    // broad 8k dual-rail cap. Raise only this local guard so whole-chip
    // surfaces still fail fast before materializing broad transition cones.
    const size_t encodingSupportLimit =
        hasLocalDualRailFinalLeafRepairSurface(problem)
            ? effectiveLocalDualRailFinalLeafEncodingSupportLimit(
                  configuredEncodingSupportLimit)
            : configuredEncodingSupportLimit;
    const bool unknownNodeCount =
        transitionEncodingNodes == 0 &&
        encodedTargets.size() > kMaxExactTransitionNodeCountHintTargets;  // LCOV_EXCL_LINE
    if (unknownNodeCount ||
        transitionEncodingNodes > encodingNodeLimit ||
        transitionSupportSymbols.size() > encodingSupportLimit) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: predecessor encoding budget exhausted targets=",
            encodedTargets.size(),
            " nodes=",
            transitionEncodingNodes,
            " node_limit=",
            encodingNodeLimit,
            " transition_support=",
            transitionSupportSymbols.size(),
            " support_limit=",
            encodingSupportLimit,
            " level=",
            level);
      }  // LCOV_EXCL_LINE
      markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  // Large dual-rail leaves disable the broad exact reset-frontier precheck to
  // protect BP-sized batches.  Once SEC has split down to one local output,
  // however, the same exact proof is cheaper than first exhausting the full
  // predecessor SAT budget on fake F0 states.  This remains a proof-only fast
  // path: if the reset query cannot prove UNSAT, the ordinary PDR predecessor
  // query below still runs unchanged.
  if (detail::shouldPrecheckLargeDualRailPredecessorWithResetFrontier(
          problem.usesDualRailStateEncoding,
          useExactResetFrontierChecks,
          problem.observedOutputExprs0.size(),
          level,
          targetCube.size(),
          transitionSupportSymbols.size(),
          localExactResetPrecheckSupportLimit)) {
    if (const auto resetPrecheck = // LCOV_EXCL_LINE
            proveLargeDualRailPredecessorWithResetFrontier( // LCOV_EXCL_LINE
                problem, // LCOV_EXCL_LINE
                solverType, // LCOV_EXCL_LINE
                transitionByState, // LCOV_EXCL_LINE
                frameInvariant, // LCOV_EXCL_LINE
                level, // LCOV_EXCL_LINE
                targetCube, // LCOV_EXCL_LINE
                transitionSupportSymbols, // LCOV_EXCL_LINE
                useExactResetFrontierChecks, // LCOV_EXCL_LINE
                localExactResetPrecheckSupportLimit, // LCOV_EXCL_LINE
                resetFrontierCache, // LCOV_EXCL_LINE
                "precheck");
        resetPrecheck.has_value()) { // LCOV_EXCL_LINE
      if (*resetPrecheck) { // LCOV_EXCL_LINE
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() && // LCOV_EXCL_LINE
            predecessorAssumptionCache != nullptr) { // LCOV_EXCL_LINE
          rememberPredecessorQueryResult( // LCOV_EXCL_LINE
              *predecessorAssumptionCache, // LCOV_EXCL_LINE
              *exactCacheKey, // LCOV_EXCL_LINE
              *stableUnsatCacheKey, // LCOV_EXCL_LINE
              std::nullopt); // LCOV_EXCL_LINE
        } // LCOV_EXCL_LINE
        return std::nullopt; // LCOV_EXCL_LINE
      }
    } // LCOV_EXCL_LINE
  } // LCOV_EXCL_LINE

  // This reset-frontier precheck is an optional accelerator for projected PDR
  // queries: it can reject fake F[0] predecessors before they become root
  // obligations. In unprojected mode the predecessor query itself is already
  // the cheapest exact PDR step available, and AES sampling showed the extra
  // reset-prefix SAT precheck becoming the wall before that query could run.
  if (useExactResetFrontierChecks &&
      !predecessorQueryIsAlreadyExact &&
      level == 0 && problem.resetBootstrapCycles != 0 &&
      resetFrontierCache != nullptr &&
      transitionSupportSymbols.size() <= localExactResetPrecheckSupportLimit) {
    // F[0] is a compact summary of the concrete post-reset image. Asking only
    // the abstract F[0] predecessor query can enumerate thousands of fake
    // reset states one refinement clause at a time. The exact reset-frontier
    // check answers the real level-0 question first: can any concrete
    // post-reset state reach this target cube in one PDR transition?
    const bool hasConcreteResetPredecessor =
        !cubeOutsideConcreteResetFrontier(
            problem,
            solverType,
            transitionByState,
            targetCube,
            1,
            *resetFrontierCache,
            false,
            // These prechecks appear in waves of neighboring PDR cubes. AES
            // sampling showed the one-shot query rebuilding and solving the
            // same reset-prefix shape for each neighbor; the cached assumption
            // path can reuse the wider solver plus failed cores across that
            // wave.
            ConcreteCubeReachabilityMode::CachedAssumptions,
            frameInvariant);
    if (emitStatsForQuery) {
      emitSecDiag(
          "SEC PDR stats: predecessor #", statsQueryNumber,
          " level=", level,
          " target_cube=", targetCube.size(),
          " target_hash=", cubeFingerprint(targetCube),
          " encoded_targets=", encodedTargets.size(),
          " transition_support=", transitionSupportSymbols.size(),
          " projection_limit=", predecessorProjectionLimit,
          " support_limit=", localExactResetPrecheckSupportLimit,
          " exact_reset_frontier=1 result=",
          hasConcreteResetPredecessor ? "sat" : "unsat");
    }
    if (!hasConcreteResetPredecessor) {
      return std::nullopt;
    }
  } else if (
      level == 0 && problem.resetBootstrapCycles != 0 &&
      resetFrontierCache != nullptr && emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " level=", level,
        " target_cube=", targetCube.size(),
        " target_hash=", cubeFingerprint(targetCube),
        " encoded_targets=", encodedTargets.size(),
        " transition_support=", transitionSupportSymbols.size(),
        " projection_limit=", predecessorProjectionLimit,
        " support_limit=", localExactResetPrecheckSupportLimit,
        " exact_reset_frontier=",
        useExactResetFrontierChecks ? "skipped" : "disabled");
  }

  // Keep this split from solverSymbols: the SAT instance may include extra
  // transition support, while the carried predecessor cube is intentionally
  // projected down to the current-frame symbols that explain the target.
  const std::vector<size_t> predecessorSymbols = predecessorProjectionSymbols(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      complementPartners,
      transitionSupportSymbols,
      supportCache);
  const std::vector<size_t> solverSymbols = predecessorCurrentFrameQuerySymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      targetCube,
      excludeTargetOnCurrentFrame,
      predecessorSymbols,
      transitionSupportSymbols,
      complementPartners,
      exactFrameClauses,
      extraFrameClauses,
      predecessorAssumptionCache,
      supportCache);
  const std::vector<size_t> cachedSolverSymbols =
      predecessorAssumptionCacheSymbols(
          problem,
          transitionByState,
          solverSymbols,
          exactFrameClauses,
          level,
          predecessorAssumptionCache);
  const unsigned predecessorConflictLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorConflictLimitForQuery(
                problem, targetCube, level, cachedSolverSymbols.size())
          : 0;
  const unsigned predecessorDecisionLimit =
      problem.usesDualRailStateEncoding
          ? dualRailPredecessorDecisionLimit(predecessorConflictLimit)
          : std::numeric_limits<unsigned>::max();
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " level=", level,
        " target_cube=", targetCube.size(),
        " target_hash=", cubeFingerprint(targetCube),
        " encoded_targets=", encodedTargets.size(),
        " transition_support=", transitionSupportSymbols.size(),
        " predecessor_symbols=", predecessorSymbols.size(),
        " solver_symbols=", solverSymbols.size(),
        " cached_solver_symbols=", cachedSolverSymbols.size(),
        " projection_limit=", predecessorProjectionLimit,
        " conflict_limit=", predecessorConflictLimit,
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " exclude_target=", excludeTargetOnCurrentFrame ? 1 : 0);
  }
  if (problem.usesDualRailStateEncoding &&
      predecessorAssumptionCache != nullptr) {
    PredecessorAssumptionSolver* solvedPredecessorCache = nullptr;
    std::vector<int> cachedAssumptions;
    StateCube cachedUnsatCore;
    auto cachedStatus = solvePredecessorCubeWithCachedAssumptions(
        *predecessorAssumptionCache,
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        level,
        targetCube,
        encodedTargets,
        transitionSupportSymbols,
        cachedSolverSymbols,
        excludeTargetOnCurrentFrame,
        extraFrameClauses,
        exactFrameClauses,
        predecessorConflictLimit,
        predecessorDecisionLimit,
        &solvedPredecessorCache,
        &cachedAssumptions,
        &cachedUnsatCore);
    if (cachedStatus.has_value() &&
        *cachedStatus == SATSolverWrapper::SolveStatus::Unknown &&
        solvedPredecessorCache != nullptr && !cachedAssumptions.empty() &&
        canRetryDualRailPredecessorInCachedSolver(problem)) {
      if (emitStatsForQuery) {
        emitSecDiag(
            "SEC PDR stats: predecessor #", statsQueryNumber,
            " cached_assumptions=unknown retry=cached_solver");
      }
      // The fresh fallback asks the same SAT question as the cached assumption
      // solver. Spend the fallback budget in that solver so learned clauses and
      // already-encoded transition/frame constraints are reused instead of
      // rebuilding large dual-rail cones for every residual predecessor.
      cachedStatus =
          solvedPredecessorCache->solver->solveWithAssumptionsStatus(
              cachedAssumptions,
              resourceLimitOrUnbounded(predecessorConflictLimit),
              resourceLimitOrUnbounded(predecessorDecisionLimit));
      if (cachedStatus.has_value() &&
          *cachedStatus == SATSolverWrapper::SolveStatus::Unknown) {
        if (const auto resetRetry = // LCOV_EXCL_LINE
                proveLargeDualRailPredecessorWithResetFrontier(
                    problem,
                    solverType,
                    transitionByState,
                    frameInvariant,
                    level,
                    targetCube,
                    transitionSupportSymbols,
                    useExactResetFrontierChecks,
                    localExactResetPrecheckSupportLimit,
                    resetFrontierCache,
                    "retry after budget");
            resetRetry.has_value() && *resetRetry) {
          if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) { // LCOV_EXCL_LINE
            rememberPredecessorQueryResult( // LCOV_EXCL_LINE
                *predecessorAssumptionCache, // LCOV_EXCL_LINE
                *exactCacheKey, // LCOV_EXCL_LINE
                *stableUnsatCacheKey, // LCOV_EXCL_LINE
                std::nullopt); // LCOV_EXCL_LINE
          } // LCOV_EXCL_LINE
          return std::nullopt; // LCOV_EXCL_LINE
        }
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: predecessor query budget exhausted limit=",
              predecessorConflictLimit,
              " decision_limit=",
              predecessorDecisionLimit,
              " symbols=",
              cachedSolverSymbols.size(),
              " level=",
              level,
              " cached_solver_retry=1");
        }
        markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);
        return std::nullopt;
      }
    } // LCOV_EXCL_LINE
    if (cachedStatus.has_value()) {
      if (*cachedStatus == SATSolverWrapper::SolveStatus::Unsat) {
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " result=unsat cached_assumptions=1");
        }
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) {
          const StateCube* cachedUnsatCorePtr =
              cachedUnsatCore.empty() ? nullptr : &cachedUnsatCore;
          rememberPredecessorQueryResult(
              *predecessorAssumptionCache,
              *exactCacheKey,
              *stableUnsatCacheKey,
              std::nullopt,
              cachedUnsatCorePtr);
        }
        return std::nullopt;
      }
      if (*cachedStatus == SATSolverWrapper::SolveStatus::Sat &&
          solvedPredecessorCache != nullptr &&
          hasLocalDualRailFinalLeafRepairSurface(problem)) {
        if (emitStatsForQuery) {
          emitSecDiag(
              "SEC PDR stats: predecessor #", statsQueryNumber,
              " result=sat cached_assumptions=1");
        }
        StateCube predecessor = extractSolvedPredecessorCube(
            *solvedPredecessorCache->solver,
            *solvedPredecessorCache->variables,
            problem,
            transitionByState,
            targetCube,
            predecessorSymbols,
            solvedPredecessorCache->transitionLeafLits,
            complementPartners,
            predecessorProjectionLimit);
        if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value()) {
          rememberPredecessorQueryResult(
              *predecessorAssumptionCache,
              *exactCacheKey,
              *stableUnsatCacheKey,
              std::optional<StateCube>(predecessor));
        }
        return predecessor;
      }
      if (emitStatsForQuery) {
        emitSecDiag(
            "SEC PDR stats: predecessor #", statsQueryNumber,
            " cached_assumptions=",
            *cachedStatus == SATSolverWrapper::SolveStatus::Sat ? "sat"
                                                                : "unknown",
            " fallback=exact");
      }
    }
  }
  const auto predecessorSolverType =
      localDualRailPredecessorSolverType(problem, solverType);
  SATSolverWrapper solver(predecessorSolverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols, exactFrameClauses);
  addSafeFramePropertyConstraint(solver, variables, problem, level, 0);
  if (extraFrameClauses != nullptr) {
    for (const auto& clause : *extraFrameClauses) {
      if (clauseCoveredByVariables(variables, clause)) {
        addStateClause(solver, variables, clause, 0);
      }
    }
  }
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  // Encode only the next-state equations needed to decide the requested target
  // cube. This keeps one local PDR obligation from materializing the entire
  // design transition relation.
  std::unordered_map<size_t, int> transitionLeafLits;
  addTransitionConstraintsForTargetCube(
      solver,
      variables,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols,
      &transitionLeafLits);
  if (excludeTargetOnCurrentFrame) {
    addNegatedCubeClause(solver, variables, targetCube, 0);
  }
  SATSolverWrapper::SolveStatus predecessorSolveStatus =
      SATSolverWrapper::SolveStatus::Sat;
  if (problem.usesDualRailStateEncoding) {
    // Predecessor queries are local PDR obligations. A limit hit is not a
    // proof of UNSAT, so dual-rail mode turns it into an inconclusive leaf
    // instead of letting one hard residual output dominate the regress run.
    predecessorSolveStatus = solver.solveWithResourceLimits(
        predecessorConflictLimit,
        predecessorDecisionLimit);
  } else {
    predecessorSolveStatus = solver.solveStatus();
  }
  if (predecessorSolveStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (const auto resetRetry = // LCOV_EXCL_LINE
            proveLargeDualRailPredecessorWithResetFrontier(
                problem,
                solverType,
                transitionByState,
                frameInvariant,
                level,
                targetCube,
                transitionSupportSymbols,
                useExactResetFrontierChecks,
                localExactResetPrecheckSupportLimit,
                resetFrontierCache,
                "retry after budget");
        resetRetry.has_value() && *resetRetry) {
      if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() && // LCOV_EXCL_LINE
          predecessorAssumptionCache != nullptr) { // LCOV_EXCL_LINE
        rememberPredecessorQueryResult( // LCOV_EXCL_LINE
            *predecessorAssumptionCache, // LCOV_EXCL_LINE
            *exactCacheKey, // LCOV_EXCL_LINE
            *stableUnsatCacheKey, // LCOV_EXCL_LINE
            std::nullopt); // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE
      return std::nullopt; // LCOV_EXCL_LINE
    }
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor query budget exhausted limit=",
          predecessorConflictLimit,
          " decision_limit=",
          predecessorDecisionLimit,
          " symbols=",
          solverSymbols.size(),
          " level=",
          level);
    }  // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery);  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const bool hasPredecessor =
      predecessorSolveStatus == SATSolverWrapper::SolveStatus::Sat;
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " result=", hasPredecessor ? "sat" : "unsat");
  }
  if (!hasPredecessor) {
    if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() &&
        predecessorAssumptionCache != nullptr) {
      rememberPredecessorQueryResult(
          *predecessorAssumptionCache,
          *exactCacheKey,
          *stableUnsatCacheKey,
          std::nullopt);
    }
    return std::nullopt;
  }
  StateCube predecessor = extractSolvedPredecessorCube(
      solver,
      variables,
      problem,
      transitionByState,
      targetCube,
      predecessorSymbols,
      transitionLeafLits,
      complementPartners,
      predecessorProjectionLimit);
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " predecessor_cube=", predecessor.size(),
        " predecessor_hash=", cubeFingerprint(predecessor));
  }
  if (exactCacheKey.has_value() && stableUnsatCacheKey.has_value() &&
      predecessorAssumptionCache != nullptr) {
    rememberPredecessorQueryResult(
        *predecessorAssumptionCache,
        *exactCacheKey,
        *stableUnsatCacheKey,
        std::optional<StateCube>(predecessor));
  }
  return predecessor;
}

bool cubeIntersectsInit(const KInductionProblem& problem,
                        KEPLER_FORMAL::Config::SolverType solverType,
                        BoolExpr* initFormula,
                        const StateCube& cube) {
  // A clause is only safe to learn if its negated cube stays outside Init.
  if (const auto knownResult = cubeIntersectsKnownInitFacts(problem, cube);
      knownResult.has_value()) {
    return *knownResult;
  }

  const std::vector<size_t> solverSymbols =
      // LCOV_EXCL_START
      initIntersectionSymbols(problem, initFormula, cube);
      // LCOV_EXCL_STOP
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  // LCOV_EXCL_START
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  // LCOV_EXCL_STOP
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  // LCOV_EXCL_START
  addSameFrameStateEqualities(solver, variables, problem, 1);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  // LCOV_EXCL_STOP
  addCubeAssumptions(solver, variables, cube, 0);
  // LCOV_EXCL_START
  return solver.solve();
}

bool appendTargetLiteral(StateCube& candidate,  // LCOV_EXCL_LINE
// LCOV_EXCL_STOP
                         const StateCube& targetCube,
                         size_t symbol) {
  if (findCubeLiteralValue(candidate, symbol).has_value()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  const auto targetValue = findCubeLiteralValue(targetCube, symbol);  // LCOV_EXCL_LINE
  if (!targetValue.has_value()) {  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  candidate.push_back({symbol, *targetValue});  // LCOV_EXCL_LINE
  normalizeCube(candidate);  // LCOV_EXCL_LINE
  return true;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

size_t cubeLiteralKey(const CubeLiteral& literal) {
  return (literal.symbol << 1) | (literal.value ? 1u : 0u);
}

std::vector<int> assumptionLiteralsForCube(
    // LCOV_EXCL_START
    const StateCube& cube,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
    // LCOV_EXCL_STOP
  std::unordered_map<size_t, int> assumptionByLiteral;
  assumptionByLiteral.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, literal] : assumptionPairs) {
    assumptionByLiteral.emplace(cubeLiteralKey(literal), assumptionLit);
  }

  // LCOV_EXCL_START
  std::vector<int> assumptions;
  // LCOV_EXCL_STOP
  assumptions.reserve(cube.size());
  for (const auto& literal : cube) {
    // LCOV_EXCL_START
    const auto it = assumptionByLiteral.find(cubeLiteralKey(literal));
    if (it == assumptionByLiteral.end()) {
      assumptions.clear();  // LCOV_EXCL_LINE
      return assumptions;  // LCOV_EXCL_LINE
    }
    assumptions.push_back(it->second);
  }
  // LCOV_EXCL_STOP
  return assumptions;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START
StateCube cubeFromAssumptionLiterals(  // LCOV_EXCL_LINE
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption) {
    // LCOV_EXCL_STOP
  StateCube cube;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  cube.reserve(assumptions.size());  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  for (const auto assumption : assumptions) {  // LCOV_EXCL_LINE
    const auto it = literalByAssumption.find(assumption);  // LCOV_EXCL_LINE
    if (it == literalByAssumption.end()) {  // LCOV_EXCL_LINE
      cube.clear();  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      return cube;  // LCOV_EXCL_LINE
    }
    cube.push_back(it->second);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  normalizeCube(cube);  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  return cube;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> minimizeCoreInTargetContext(  // LCOV_EXCL_LINE
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks) {
  std::vector<int> candidate = assumptions;  // LCOV_EXCL_LINE
  if (candidate.empty()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  // LCOV_EXCL_START
  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);  // LCOV_EXCL_LINE
       chunkSize > 0 &&  // LCOV_EXCL_LINE
       *checks < kMaxPredecessorCoreContextMinimizationChecks;) {  // LCOV_EXCL_LINE
    bool removedAny = false;  // LCOV_EXCL_LINE
    for (size_t index = 0;  // LCOV_EXCL_LINE
         index < candidate.size() &&  // LCOV_EXCL_LINE
         *checks < kMaxPredecessorCoreContextMinimizationChecks;) {  // LCOV_EXCL_LINE
         // LCOV_EXCL_STOP
      const size_t erasedCount =  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          std::min(chunkSize, candidate.size() - index);  // LCOV_EXCL_LINE
      if (erasedCount == 0 || erasedCount == candidate.size()) {  // LCOV_EXCL_LINE
        break;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP

      // LCOV_EXCL_START
      std::vector<int> trial = candidate;  // LCOV_EXCL_LINE
      trial.erase(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          trial.begin() + static_cast<std::ptrdiff_t>(index),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          trial.begin() +  // LCOV_EXCL_LINE
              static_cast<std::ptrdiff_t>(index + erasedCount));  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
      ++(*checks);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto status = coreSolver.solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
          trial, kPredecessorCoreConflictLimit);
          // LCOV_EXCL_STOP
      if (status == SATSolverWrapper::SolveStatus::Unsat) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        candidate = std::move(trial);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        removedAny = true;  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      index += erasedCount;  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE


// LCOV_EXCL_STOP
    if (chunkSize == 1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      break;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
    if (!removedAny && chunkSize == 1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      break;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);  // LCOV_EXCL_LINE
  }

  StateCube minimized = cubeFromAssumptionLiterals(  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      candidate, literalByAssumption);  // LCOV_EXCL_LINE
  if (minimized.empty()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  return minimized;  // LCOV_EXCL_LINE
// LCOV_EXCL_START
}  // LCOV_EXCL_LINE

std::optional<StateCube> growCoreOutsideInit(  // LCOV_EXCL_LINE
// LCOV_EXCL_STOP
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    // LCOV_EXCL_STOP
    const StateCube& core,
    // LCOV_EXCL_START
    const StateCube& targetCube) {
  StateCube candidate = core;  // LCOV_EXCL_LINE
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {  // LCOV_EXCL_LINE
    return candidate;  // LCOV_EXCL_LINE
  }

  auto tryAddSymbol = [&](size_t symbol) -> bool {  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
    if (!appendTargetLiteral(candidate, targetCube, symbol)) {  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    return !cubeIntersectsInit(problem, solverType, initFormula, candidate);  // LCOV_EXCL_LINE
  };  // LCOV_EXCL_LINE

// LCOV_EXCL_START

  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;  // LCOV_EXCL_LINE
  const auto& assignments = usesBootstrapFrontier  // LCOV_EXCL_LINE
                                ? problem.bootstrapStateAssignments  // LCOV_EXCL_LINE
                                : problem.initialStateAssignments;  // LCOV_EXCL_LINE
                                // LCOV_EXCL_STOP
  const auto& equalities =  // LCOV_EXCL_LINE
      KEPLER_FORMAL::Config::getSecInternalStateCorrespondence() // LCOV_EXCL_LINE
          ? (usesBootstrapFrontier  // LCOV_EXCL_LINE
                 ? problem.bootstrapStateEqualityPairs  // LCOV_EXCL_LINE
                 // LCOV_EXCL_START
                 : problem.initialStateEqualityPairs)  // LCOV_EXCL_LINE
          : emptySymbolPairs();  // LCOV_EXCL_LINE

  // UNSAT cores from transition assumptions can be too small to be legal PDR
  // frame clauses because a one-bit reason may still overlap Init. Add only
  // original target literals until the cube visibly contradicts Init; the
  // predecessor UNSAT result is monotonic under this strengthening.
  // LCOV_EXCL_STOP
  for (const auto& [symbol, initValue] : assignments) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto targetValue = findCubeLiteralValue(targetCube, symbol);  // LCOV_EXCL_LINE
    if (targetValue.has_value() && *targetValue != initValue &&  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
        tryAddSymbol(symbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {  // LCOV_EXCL_LINE
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);  // LCOV_EXCL_LINE
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);  // LCOV_EXCL_LINE
    if (!lhsTargetValue.has_value() || !rhsTargetValue.has_value() ||  // LCOV_EXCL_LINE
        *lhsTargetValue == *rhsTargetValue) {  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    // LCOV_EXCL_START
    if (tryAddSymbol(lhsSymbol) || tryAddSymbol(rhsSymbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto lhsCoreValue = findCubeLiteralValue(candidate, lhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    const auto rhsCoreValue = findCubeLiteralValue(candidate, rhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);  // LCOV_EXCL_LINE
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (lhsCoreValue.has_value() && rhsTargetValue.has_value() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        *lhsCoreValue != *rhsTargetValue && tryAddSymbol(rhsSymbol)) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      return candidate;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    if (rhsCoreValue.has_value() && lhsTargetValue.has_value() &&  // LCOV_EXCL_LINE
        *rhsCoreValue != *lhsTargetValue && tryAddSymbol(lhsSymbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  if (problem.complementedStatePairs0.size() <=  // LCOV_EXCL_LINE
      kMaxComplementPairsForCheapInitCheck) {
      // LCOV_EXCL_STOP
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
         problem.complementedStatePairs0) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto complementedTargetValue =
          // LCOV_EXCL_START
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (!primaryTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          !complementedTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          *primaryTargetValue != *complementedTargetValue) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        continue;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
      // LCOV_EXCL_START
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
         problem.complementedStatePairs0) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);  // LCOV_EXCL_LINE
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          *primaryCoreValue == *complementedTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        return candidate;  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          *complementedCoreValue == *primaryTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(primarySymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (problem.complementedStatePairs1.size() <=  // LCOV_EXCL_LINE
      kMaxComplementPairsForCheapInitCheck) {
      // LCOV_EXCL_STOP
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
         problem.complementedStatePairs1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto complementedTargetValue =
          // LCOV_EXCL_START
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      if (!primaryTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          !complementedTargetValue.has_value() ||  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          *primaryTargetValue != *complementedTargetValue) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        continue;  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      }
      // LCOV_EXCL_START
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
        return candidate;  // LCOV_EXCL_LINE
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
         problem.complementedStatePairs1) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);  // LCOV_EXCL_LINE
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const auto complementedTargetValue =
      // LCOV_EXCL_STOP
          findCubeLiteralValue(targetCube, complementedSymbol);  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&  // LCOV_EXCL_LINE
          *primaryCoreValue == *complementedTargetValue &&  // LCOV_EXCL_LINE
          tryAddSymbol(complementedSymbol)) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        return candidate;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_START
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&  // LCOV_EXCL_LINE
          *complementedCoreValue == *primaryTargetValue &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          tryAddSymbol(primarySymbol)) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return candidate;  // LCOV_EXCL_LINE
      }
      // LCOV_EXCL_STOP
    }
  }  // LCOV_EXCL_LINE

  for (const auto& literal : targetCube) {  // LCOV_EXCL_LINE
    if (tryAddSymbol(literal.symbol)) {  // LCOV_EXCL_LINE
      return candidate;  // LCOV_EXCL_LINE
    }
  }
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {  // LCOV_EXCL_LINE
    return candidate;  // LCOV_EXCL_LINE
  }
  return std::nullopt;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

std::optional<StateCube> findValidatedPredecessorCore(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t sourceLevel,
    const StateCube& targetCube,
    ResetFrontierCache* resetFrontierCache,
    PredecessorAssumptionCache* predecessorAssumptionCache,
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses,
    bool useExactResetFrontierChecks,
    size_t* predecessorQueryBudget,
    PdrFormulaSupportCache* supportCache) {
  // For source level zero, the learned clause is placed in F1 and only needs
  // the concrete "F0 cannot transition to core'" check.  Higher levels use the
  // usual relative-induction check and may rely on excluding the candidate cube
  // from the current frame because that clause is already present there.
  const bool excludeCurrentTargetForCore = sourceLevel != 0;
  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
  const std::vector<size_t> predecessorSymbols = predecessorProjectionSymbols(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      complementPartners,
      transitionSupportSymbols,
      supportCache);
  const std::vector<size_t> solverSymbols = predecessorCurrentFrameQuerySymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      targetCube,
      excludeCurrentTargetForCore,
      predecessorSymbols,
      transitionSupportSymbols,
      complementPartners,
      exactFrameClauses,
      nullptr,
      predecessorAssumptionCache,
      supportCache);

  // Use an assumption-capable solver here only as an UNSAT-core oracle over
  // the target literals. Any proposed smaller cube is revalidated below with
  // the normal PDR predecessor query before it can become a learned frame
  // clause.
  SATSolverWrapper coreSolver(
      SATSolverWrapper::assumptionSolverTypeFor(solverType));
  coreSolver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(coreSolver, solverSymbols, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(
      coreSolver, variables, problem.complementedStatePairs1, 1);
  addSameFrameStateEqualities(coreSolver, variables, problem, 1);
  addDualRailStateValidity(coreSolver, variables, problem.dualRailStatePairs, 1);
  addFrameConstraints(
      // LCOV_EXCL_START
      coreSolver,
      variables,
      // LCOV_EXCL_STOP
      problem,
      initFormula,
      frameInvariant,
      frames,
      sourceLevel,
      0,
      solverSymbols,
      exactFrameClauses);
  addSafeFramePropertyConstraint(coreSolver, variables, problem, sourceLevel, 0);
  addPostBootstrapResetInputConstraints(coreSolver, variables, problem, 0);
  // LCOV_EXCL_START
  if (excludeCurrentTargetForCore) {
    addNegatedCubeClause(coreSolver, variables, targetCube, 0);  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE

// LCOV_EXCL_START


// LCOV_EXCL_STOP
  const auto assumptionPairs = addTransitionAssumptionsForTargetCube(
      coreSolver,
      variables,
      // LCOV_EXCL_START
      transitionByState,
      0,
      targetCube,
      // LCOV_EXCL_STOP
      encodedTargets,
      transitionSupportSymbols);
  if (assumptionPairs.empty()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=empty_assumptions target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  // LCOV_EXCL_START
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
  // LCOV_EXCL_STOP
    assumptions.push_back(assumptionLit);
    // LCOV_EXCL_START
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // LCOV_EXCL_STOP
    // Assumption-core solvers may report final conflicts in solver-literal polarity. Map both
    // signs back to the requested cube literal and let exact revalidation below
    // decide whether the proposed core is usable.
    // LCOV_EXCL_START
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }


// LCOV_EXCL_STOP
  const auto coreQueryStatus = coreSolver.solveWithAssumptionsStatus(
      assumptions, kPredecessorCoreConflictLimit);
  // LCOV_EXCL_START
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Sat) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          "SEC PDR stats: predecessor core miss reason=core_query_sat target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          " source_level=",
          sourceLevel,
          " target_hash=",
          // LCOV_EXCL_START
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=resource_limit target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " source_level=",
          // LCOV_EXCL_STOP
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }


// LCOV_EXCL_STOP
  StateCube core;
  // LCOV_EXCL_START
  const auto failedAssumptions = coreSolver.failedAssumptions();
  // LCOV_EXCL_STOP
  for (const auto failedLit : failedAssumptions) {
    const auto it = literalByAssumption.find(failedLit);
    if (it == literalByAssumption.end()) {
      // LCOV_EXCL_START
      continue;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    }
    // LCOV_EXCL_START
    core.push_back(it->second);
    // LCOV_EXCL_STOP
  }
  // LCOV_EXCL_START
  normalizeCube(core);
  if (core.empty() || core.size() >= targetCube.size()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=not_smaller target=",
          targetCube.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " failed_assumptions=",
          failedAssumptions.size(),  // LCOV_EXCL_LINE
          " mapped_core=",
          core.size(),  // LCOV_EXCL_LINE
          " target_hash=",
          cubeFingerprint(targetCube));  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }

  if (sourceLevel != 0) {
    // For higher frames the generalized clause is pushed into earlier learned
    // LCOV_EXCL_STOP
    // frames as well, so keep the standard IC3/PDR requirement that the reduced
    // LCOV_EXCL_START
    // cube excludes Init.  Source level zero is different in this implementation:
    // LCOV_EXCL_STOP
    // F0 is the already-checked startup frontier and the learned clause is only
    // LCOV_EXCL_START
    // placed in F1, so the exact no-predecessor query from F0 is the required
    // LCOV_EXCL_STOP
    // safety check.  BlackParrot sampling showed thousands of repeated
    // source_level=0 core misses when we unnecessarily rejected those cores for
    // overlapping Init.
    // LCOV_EXCL_START
    const auto initSafeCore = growCoreOutsideInit(  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
        problem, solverType, initFormula, core, targetCube);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (!initSafeCore.has_value() || initSafeCore->size() >= targetCube.size()) {  // LCOV_EXCL_LINE
      if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
          targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
        emitSecDiag(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            "SEC PDR stats: predecessor core miss reason=init_intersection target=",
            targetCube.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            "->",
            core.size(),  // LCOV_EXCL_LINE
            " source_level=",
            sourceLevel,
            " target_hash=",
            cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
            " core_hash=",
            cubeFingerprint(core));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    core = *initSafeCore;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE

  std::vector<int> coreAssumptions =
      // LCOV_EXCL_START
      assumptionLiteralsForCube(core, assumptionPairs);
  bool coreBlockedInTargetContext = false;
  // LCOV_EXCL_STOP
  bool coreContextResourceLimited = false;
  if (coreAssumptions.size() == core.size()) {
    const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(
        coreAssumptions, kPredecessorCoreConflictLimit);
    // LCOV_EXCL_START
    coreBlockedInTargetContext =
    // LCOV_EXCL_STOP
        coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;
    coreContextResourceLimited =
        coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;
  }
  // LCOV_EXCL_START
  size_t contextMinimizationChecks = 0;
  if (!coreBlockedInTargetContext &&
      !coreContextResourceLimited &&  // LCOV_EXCL_LINE
      targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // The failed-assumption vector is only a seed. If it is not itself UNSAT,
    // minimize the full target assumption set in the same solver context. This
    // LCOV_EXCL_STOP
    // keeps the proof obligation honest: every accepted reduced cube is backed
    // LCOV_EXCL_START
    // by an actual UNSAT predecessor query, not by solver-conflict bookkeeping.
    if (const auto minimizedCore = minimizeCoreInTargetContext(  // LCOV_EXCL_LINE
            coreSolver,
            assumptions,
            literalByAssumption,
            &contextMinimizationChecks);
        minimizedCore.has_value() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        minimizedCore->size() < targetCube.size()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      core = *minimizedCore;  // LCOV_EXCL_LINE
      coreAssumptions = assumptionLiteralsForCube(core, assumptionPairs);  // LCOV_EXCL_LINE
      if (coreAssumptions.size() == core.size()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
        const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            coreAssumptions, kPredecessorCoreConflictLimit);
            // LCOV_EXCL_STOP
        coreBlockedInTargetContext =  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
        coreContextResourceLimited =  // LCOV_EXCL_LINE
            coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (!coreBlockedInTargetContext) {
  // LCOV_EXCL_STOP
    if (pdrStatsEnabled() &&  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=context_core_sat target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          "->",
          // LCOV_EXCL_STOP
          core.size(),  // LCOV_EXCL_LINE
          " source_level=",
          sourceLevel,
          " resource_limit=",
          coreContextResourceLimited ? "true" : "false",  // LCOV_EXCL_LINE
          " target_hash=",
          cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
          " core_hash=",
          cubeFingerprint(core),  // LCOV_EXCL_LINE
          " context_checks=",
          contextMinimizationChecks);
    }  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (sourceLevel == 0) {
    // The core came from, and is rechecked in, the full target-context
    // predecessor query. This is stronger than rebuilding a narrower
    // one-literal query: all included frame clauses, reset-input constraints,
    // complemented-state relations, and target-cone transition definitions are
    // real PDR constraints. If that context cannot reach the reduced cube from
    // F0, the learned clause is safe for F1. Re-running a smaller query can
    // lose exactly the context that proved the core and was measured on
    // BlackParrot as repeated 116->1 false misses.
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor core target=",
          targetCube.size(),
          "->",
          core.size(),
          // LCOV_EXCL_START
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " validation=target_context",
          " context_checks=",
          // LCOV_EXCL_STOP
          contextMinimizationChecks);
    // LCOV_EXCL_START
    }
    return core;
  }

  const auto corePredecessor = findPredecessorCube(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      problem,  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      solverType,  // LCOV_EXCL_LINE
      transitionByState,  // LCOV_EXCL_LINE
      initFormula,  // LCOV_EXCL_LINE
      frameInvariant,  // LCOV_EXCL_LINE
      frames,  // LCOV_EXCL_LINE
      sourceLevel,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      core,
      // LCOV_EXCL_START
      excludeCurrentTargetForCore,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      complementPartners,  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      predecessorProjectionLimit,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      exactFrameClauses,  // LCOV_EXCL_LINE
      resetFrontierCache,  // LCOV_EXCL_LINE
      predecessorAssumptionCache,  // LCOV_EXCL_LINE
      nullptr,
      // LCOV_EXCL_START
      predecessorQueryBudget,  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      useExactResetFrontierChecks,  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      supportCache);  // LCOV_EXCL_LINE
  if (hasPdrBudgetExhaustion()) {  // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  if (corePredecessor.has_value()) {  // LCOV_EXCL_LINE
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: predecessor core miss reason=predecessor_exists target=",
          // LCOV_EXCL_START
          targetCube.size(),  // LCOV_EXCL_LINE
          "->",
          // LCOV_EXCL_STOP
          core.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " source_level=",
          // LCOV_EXCL_STOP
          sourceLevel,
          // LCOV_EXCL_START
          " target_hash=",
          // LCOV_EXCL_STOP
          cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
          " core_hash=",
          cubeFingerprint(core));  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    return std::nullopt;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }

  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: predecessor core target=",
        targetCube.size(),  // LCOV_EXCL_LINE
        "->",
        core.size(),  // LCOV_EXCL_LINE
        " source_level=",
        sourceLevel,
        " target_hash=",
        cubeFingerprint(targetCube),  // LCOV_EXCL_LINE
        " core_hash=",
        cubeFingerprint(core));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return core;  // LCOV_EXCL_LINE
}

StateCube generalizeBlockedCube(const KInductionProblem& problem,
                                KEPLER_FORMAL::Config::SolverType solverType,
                                const TransitionExprResolver& transitionByState,
                                BoolExpr* initFormula,
                                BoolExpr* frameInvariant,
                                const std::vector<FrameClauses>& frames,
                                size_t level,
                                const StateCube& cube,
                                ResetFrontierCache* resetFrontierCache,
                                PredecessorAssumptionCache* predecessorAssumptionCache,
                                const ComplementPartnerIndex& complementPartners,
                                size_t predecessorProjectionLimit,
                                bool exactFrameClauses,
                                bool useExactResetFrontierChecks,
                                size_t* predecessorQueryBudget,
                                PdrFormulaSupportCache* supportCache) {
  // Clause generalization for ordinary PDR blocking.  A candidate reduction is
  // accepted only when two proof obligations still hold:
  //   1. Init cannot already satisfy the reduced cube, so the clause is safe in
  //      every non-zero frame.
  //   2. F[level-1] cannot transition into the reduced cube, so the clause is
  //      inductive relative to the previous frame.
  //
  // The validation remains exact; the optimization is only in the search order.
  // Large output slices often produce model cubes where many adjacent literals
  // are irrelevant.  Trying to remove chunks first gives PDR compact clauses
  // without requiring an unsat-core API from the underlying SAT solver.
  size_t checks = 0;
  const size_t checkLimit =
      cube.size() > kLargeBlockedCubeGeneralizationThreshold
          ? kMaxLargeBlockedCubeGeneralizationChecks
          : kMaxSmallBlockedCubeGeneralizationChecks;
  const size_t blockedCubeSupportSize =
      blockedCubeTransitionSupportSize(problem, transitionByState, cube);
  const bool cheapTransitionSurface =
      blockedCubeSupportSize <= kCheapBlockedCubeTransitionSupportLimit;
  const bool broadDualRailTransitionSurface =
      problem.usesDualRailStateEncoding &&
      blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport;
  const bool localDualRailTransitionSurface =
      broadDualRailTransitionSurface &&
      isLocalDualRailPredecessorCoreSurface(
          level, cube.size(), blockedCubeSupportSize);
  const size_t effectiveCheckLimit =
      cheapTransitionSurface
          ? std::max(
                checkLimit,
                std::min(
                    kMaxCheapBlockedCubeGeneralizationChecks,
                    std::max(cube.size() * 2, checkLimit)))
          : checkLimit;
  const bool shouldTryPredecessorCore =
      level <= kMaxPredecessorCoreGeneralizationLevel &&
      (!broadDualRailTransitionSurface || localDualRailTransitionSurface) &&
      !cheapTransitionSurface &&
      (cube.size() > kLargeBlockedCubeGeneralizationThreshold ||
       (cube.size() >= kMinMediumCubePredecessorCoreTargetSize &&
        blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport) ||
       localDualRailTransitionSurface);
  const bool skipDualRailPredecessorCore =
      broadDualRailTransitionSurface && !localDualRailTransitionSurface;
  const size_t dualRailCoreSkipNumber = skipDualRailPredecessorCore
                                            ? nextPdrDualRailPredecessorCoreSkipNumber()
                                            : 0;
  if (skipDualRailPredecessorCore &&
      shouldEmitPdrStats(dualRailCoreSkipNumber)) {  // LCOV_EXCL_LINE
    // Predecessor-core extraction is optional clause minimization. In dual-rail
    // mode the target cube already contains rail-expanded state, and sampled
    // Swerv regressions showed the core SAT query becoming the runtime wall.
    // Learning the already-proven cube below remains sound; it only gives up
    // this local strengthening shortcut for broad rail surfaces.
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: skipped dual-rail predecessor core ",
        "cube=", cube.size(),
        // LCOV_EXCL_START
        " level=", level,
        " support=", blockedCubeSupportSize);
        // LCOV_EXCL_STOP
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (level == 1 && resetFrontierCache != nullptr &&
      problem.resetBootstrapCycles != 0) {
      // LCOV_EXCL_STOP
    // A failed exact reset-frontier predecessor precheck already proved that
    // this F1 target has no concrete post-reset predecessor. Reuse the
    // LCOV_EXCL_START
    // CaDiCaL failed-assumption core recorded by that check before the generic
    // broad-support guard falls back to learning the whole cube verbatim.
    // LCOV_DISABLED_START
    // LCOV_DISABLED_STOP
    if (const auto resetCore =
            findPdrResetUnreachableCoreForCube(*resetFrontierCache, cube, 1);
        resetCore.has_value() && resetCore->size() < cube.size()) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: reset-predecessor core ",
            "cube=", cube.size(),  // LCOV_EXCL_LINE
            "->", resetCore->size(),  // LCOV_EXCL_LINE
            " level=", level,
            " support=", blockedCubeSupportSize,
            " hash=", cubeFingerprint(*resetCore));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      return *resetCore;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_STOP
  }
  if (skipDualRailPredecessorCore &&
      predecessorAssumptionCache != nullptr &&
      canUsePredecessorQueryResultCache(problem)) {
    // The predecessor query that proved this obligation blocked already ran
    // through the cached assumption solver. Reuse its exact failed-assumption
    // core before the broad dual-rail guard below gives up on strengthening.
    // For frames above F1, keep the standard PDR init-safety check before
    // learning the smaller clause.
    if (const auto cachedCore = cachedPredecessorUnsatCoreForCube(
            *predecessorAssumptionCache,
            problem,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            /*sourceLevel=*/level - 1,
            cube,
            /*excludeTargetOnCurrentFrame=*/false,
            predecessorProjectionLimit,
            exactFrameClauses);
        cachedCore.has_value() && cachedCore->size() < cube.size() &&
        (level == 1 ||
         !cubeIntersectsInit(problem, solverType, initFormula, *cachedCore))) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: predecessor cached core target=",
            cube.size(),
            "->",
            cachedCore->size(),
            " source_level=",
            level - 1,
            " target_hash=",
            cubeFingerprint(cube),
            " core_hash=",
            cubeFingerprint(*cachedCore),
            " support=",
            blockedCubeSupportSize);
      }
      return *cachedCore;
    }
  } // LCOV_EXCL_LINE
  if (shouldTryPredecessorCore) {
    // For wide blockers, ask the SAT solver for the actual predecessor UNSAT
    // reason before spending bounded chunk-dropping checks. BlackParrot samples
    // showed both wide 68/88-literal blockers and medium 37-49-literal blockers
    // with huge transition support where the conflict core was one or two
    // literals; without this step PDR learned thousands of adjacent clauses.
    if (const auto core = findValidatedPredecessorCore(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            // LCOV_EXCL_START
            frames,
            // LCOV_EXCL_STOP
            level - 1,
            cube,
            // LCOV_EXCL_START
            resetFrontierCache,
            predecessorAssumptionCache,
            // LCOV_EXCL_STOP
            complementPartners,
            predecessorProjectionLimit,
            exactFrameClauses,
            useExactResetFrontierChecks,
            predecessorQueryBudget,
            // LCOV_EXCL_START
            supportCache);
            // LCOV_EXCL_STOP
        core.has_value()) {
      // LCOV_EXCL_START
      return *core;
      // LCOV_EXCL_STOP
    }
  }  // LCOV_EXCL_LINE
  if (!cheapTransitionSurface &&
      cube.size() > kVeryLargeBlockedCubeGeneralizationBypassThreshold) {
    if (level != 1) {  // LCOV_EXCL_LINE
      // Keep the measured benefit of the assumption-core pass above:
      // BlackParrot wide level-1 blockers often collapse from ~100 state bits
      // to a few literals.  If no validated core is available at higher
      // levels, skip slower chunk-dropping probes and learn the already-proven
      // cube verbatim.
      return cube;  // LCOV_EXCL_LINE
    }
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (!cheapTransitionSurface &&
  // LCOV_EXCL_STOP
      blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport) {
    // Generalization is only a clause-strengthening optimization.  When the
    // target cube depends on a broad transition surface, every literal-dropping
    // probe rebuilds and solves an expensive predecessor query.  Learn the
    // already-proven blocked cube verbatim instead of spending ASIC runtime on
    // optional minimization work.
    return cube;
  }

  const bool blocksFromInitialFrame = level == 1;
  auto reductionStillBlocks = [&](const StateCube& reduced) {
    if (reduced.empty()) {
      return false;  // LCOV_EXCL_LINE
    }
    if (!blocksFromInitialFrame &&
        cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      return false;
    }
    const auto predecessor = findPredecessorCube(
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        level - 1,
        reduced,
        !blocksFromInitialFrame,
        complementPartners,
        predecessorProjectionLimit,
        exactFrameClauses,
        resetFrontierCache,
        predecessorAssumptionCache,
        nullptr,
        predecessorQueryBudget,
        useExactResetFrontierChecks,
        supportCache);
    if (hasPdrBudgetExhaustion()) {
      return false;  // LCOV_EXCL_LINE
    }
    return !predecessor.has_value();
  // LCOV_EXCL_START
  };


// LCOV_EXCL_STOP
  StateCube candidate = cube;
  if (cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // Large SAT-model cubes often contain a few cheap literals that already
    // explain the blocked transition plus hundreds of unrelated support bits.
    // Try that cheap seed first so generalization does not spend its budget on
    // giant intermediate cubes whose transition cones dominate runtime.
    const StateCube cheapSeed = boundedCheapTransitionCube(
        cube, kLargeBlockedCubeSeedSize, problem, transitionByState);
    // LCOV_EXCL_START
    if (cheapSeed.size() < cube.size() && checks < checkLimit) {
      ++checks;
      // LCOV_EXCL_STOP
      if (reductionStillBlocks(cheapSeed)) {
        candidate = cheapSeed;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
    // On ASIC SEC slices, the predecessor query itself is usually the
    // LCOV_EXCL_START
    // expensive part. Once a large cube is known blockable, spending dozens
    // LCOV_EXCL_STOP
    // more predecessor SAT calls to shave a few extra literals often costs more
    // than the smaller clause saves later. The exception is a measured cheap
    // LCOV_EXCL_START
    // transition surface: then the extra checks cost little and prevent PDR
    // from enumerating thousands of adjacent trivially unreachable cubes.
    // LCOV_EXCL_STOP
    if (!cheapTransitionSurface) {
      if (pdrStatsEnabled() && candidate.size() != cube.size()) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        emitSecDiag(  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
            "SEC PDR stats: generalized blocked cube level=",
            level,
            " size=",
            // LCOV_EXCL_START
            cube.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            "->",
            // LCOV_EXCL_START
            candidate.size(),  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            " checks=",
            checks);
      // LCOV_EXCL_START
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return candidate;  // LCOV_EXCL_LINE
    }
    if (pdrStatsEnabled() && candidate.size() != cube.size()) {
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: generalized blocked cube level=",
          level,
          " size=",
          cube.size(),  // LCOV_EXCL_LINE
          "->",
          candidate.size(),  // LCOV_EXCL_LINE
          " checks=",
          checks);
    }  // LCOV_EXCL_LINE
  }

  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);
       chunkSize > 0 && checks < effectiveCheckLimit;) {
    for (size_t index = 0;
         index < candidate.size() &&
         checks < effectiveCheckLimit;) {
      const size_t erasedCount =
          std::min(chunkSize, candidate.size() - index);
      if (erasedCount == 0 || erasedCount == candidate.size()) {
        break;
      }

      ++checks;
      StateCube reduced = candidate;
      reduced.erase(
          reduced.begin() + static_cast<std::ptrdiff_t>(index),
          reduced.begin() +
              static_cast<std::ptrdiff_t>(index + erasedCount));
      if (reductionStillBlocks(reduced)) {
        candidate = std::move(reduced);
        continue;
      }
      index += erasedCount;
    }

    if (chunkSize == 1) {
      break;
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);
  }

  if (pdrStatsEnabled() && candidate.size() != cube.size()) {
    emitSecDiag(
        "SEC PDR stats: generalized blocked cube level=",
        level,
        " size=",
        cube.size(),
        "->",
        candidate.size(),
        " checks=",
        checks);
  }
  return candidate;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.clauses.size() != rhs.clauses.size()) {
    return false;
  }
  for (const auto& clause : lhs.clauses) {
    if (!frameHasSubsumingClause(rhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
  for (const auto& clause : rhs.clauses) {
    if (!frameHasSubsumingClause(lhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return true;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START
bool obligationAlreadyBlocked(const std::vector<FrameClauses>& frames,
// LCOV_EXCL_STOP
                              const ProofObligation& obligation) {
  return frameHasSubsumingClause(frames[obligation.level], clauseFromCube(obligation.cube));
}  // LCOV_EXCL_LINE

size_t learnExactResetPredecessorSingletonClauses(
    std::vector<FrameClauses>& frames,
    const ResetFrontierCache& resetFrontierCache,
    const StateCube& sourceCube,
    size_t level) {
  if (level != 1) {
    return 0;
  }

  size_t added = 0;
  // Exact reset-predecessor cores are concrete F1 facts: no reset-frontier
  // state can step into the singleton target. Learn all sibling singletons now
  // so the bad-cube SAT query does not rediscover the same bus slice one model
  // at a time.
  for (const auto& core :
       findPdrResetUnreachableSingletonCoresForCube(
           resetFrontierCache, sourceCube, /*postBootstrapSteps=*/1)) {
    if (addClauseToFrames(frames, clauseFromCube(core), level)) {
      ++added;
    }
  }
  if (pdrStatsEnabled() && added != 0) {
    emitSecDiag(
        "SEC PDR stats: learned exact reset-predecessor singleton clauses ",
        "level=", level,
        " added=", added,
        " source_cube=", sourceCube.size());
  }
  return added;
}

size_t seedImportedResetPredecessorClauses(
    std::vector<FrameClauses>& frames,
    const ResetFrontierCache& resetFrontierCache) {
  if (frames.size() <= 1) {
    return 0;  // LCOV_EXCL_LINE
  }
  const auto stepCores =
      resetFrontierCache.resetUnreachableCoresByPostBootstrapStep.find(1);
  if (stepCores ==
      resetFrontierCache.resetUnreachableCoresByPostBootstrapStep.end()) {
    return 0;
  }

  size_t added = 0; // LCOV_EXCL_LINE
  for (const StateCube& core : stepCores->second) { // LCOV_EXCL_LINE
    // Imported reset-predecessor cores are exact F1 facts. Seeding them before
    // the first bad-state query lets later output slices consume concrete reset
    // knowledge learned by earlier slices without re-solving the same
    // reset-frontier obligations.
    if (!core.empty() && // LCOV_EXCL_LINE
        addClauseToFrames(frames, clauseFromCube(core), /*maxLevel=*/1)) { // LCOV_EXCL_LINE
      ++added; // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled() && added != 0) { // LCOV_EXCL_LINE
    emitSecDiag( // LCOV_EXCL_LINE
        "SEC PDR stats: seeded imported reset-predecessor clauses ",
        "level=1 added=", added);
  } // LCOV_EXCL_LINE
  return added; // LCOV_EXCL_LINE
}

BoolExpr* boundedResetReachabilityFrameInvariant(BoolExpr* frameInvariant) {
  if (frameInvariant == nullptr) {
    return nullptr;
  }
  if (frameInvariant->getSupportVars().size() >  // LCOV_EXCL_LINE
      kMaxResetReachabilityFrameInvariantSupport) {
    return nullptr;  // LCOV_EXCL_LINE
  }
  return frameInvariant;  // LCOV_EXCL_LINE
}

ResetFrontierReachabilityContext& resetReachabilityContextFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant) {
  frameInvariant = boundedResetReachabilityFrameInvariant(frameInvariant);
  const bool frameInvariantChanged =
      cache.reachabilityFrameInvariant != frameInvariant;
  if (cache.reachabilityContext == nullptr || frameInvariantChanged) {
    // The optional invariant changes the SAT formula for reset-frontier
    // reachability. Rebuild the immutable context and drop cached SAT answers
    // when switching between invariant-strengthened and plain checks. If the
    // context was only released for memory, cached outside facts are still
    // valid for the same invariant and should survive the rebuild.
    cache.reachabilityContext =
        makeResetFrontierReachabilityContext(
            problem, transitionByState, frameInvariant);
    cache.reachabilityFrameInvariant = frameInvariant;
    if (frameInvariantChanged) {
      cache.outsideByCubeKey.clear(); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
  }
  return *cache.reachabilityContext;
}

void rememberExactResetFrontierUnreachableCore(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  auto& reachabilityContext =
      resetReachabilityContextFor(cache, problem, transitionByState, frameInvariant);
  const auto core = findResetFrontierUnreachableCubeCore(
      reachabilityContext,
      solverType,
      cubeAssignments(cube),
      postBootstrapSteps);
  StateCube pdrCore = core.has_value() ? cubeFromAssignments(*core) : cube;
  pdrCore = minimizeExactResetPredecessorCore(
      reachabilityContext, solverType, std::move(pdrCore), postBootstrapSteps);
  if (pdrStatsEnabled() && pdrCore.size() < cube.size()) {
    emitSecDiag(
        "SEC PDR stats: exact reset-predecessor core ",
        "cube=", cube.size(),
        "->", pdrCore.size(),
        " post_bootstrap_steps=", postBootstrapSteps,
        " hash=", cubeFingerprint(pdrCore));
  }
  rememberPdrResetUnreachableCore(
      cache,
      pdrCore,
      postBootstrapSteps);
  const size_t seededSiblingCores = seedExactResetPredecessorSiblingCores(
      cache,
      reachabilityContext,
      solverType,
      cube,
      pdrCore,
      postBootstrapSteps);
  if (pdrStatsEnabled() && seededSiblingCores != 0) {
    emitSecDiag(
        "SEC PDR stats: seeded exact reset-predecessor sibling cores ",
        "cube=", cube.size(),
        " seeded=", seededSiblingCores,
        " post_bootstrap_steps=", postBootstrapSteps,
        " cached=", seededSiblingCores);
  }
}

std::optional<StateCube> proveLargeDualRailSingletonResetFrontierCore(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode,
    BoolExpr* frameInvariant) {
  if (!hasLargeDualRailResetFrontierSurface(problem) ||
      postBootstrapSteps == 0 || cube.size() <= 1) {
    return std::nullopt;
  }

  std::vector<CubeLiteral> orderedLiterals = cube;
  std::sort(
      orderedLiterals.begin(),
      orderedLiterals.end(),
      [&](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        const size_t lhsCost =
            transitionLiteralCost(problem, transitionByState, lhs.symbol);
        const size_t rhsCost =
            transitionLiteralCost(problem, transitionByState, rhs.symbol);
        if (lhsCost != rhsCost) {
          return lhsCost < rhsCost;
        }
        if (lhs.symbol != rhs.symbol) { // LCOV_EXCL_LINE
          return lhs.symbol < rhs.symbol; // LCOV_EXCL_LINE
        }
        return lhs.value < rhs.value; // LCOV_EXCL_LINE
      });

  size_t probes = 0;
  for (const auto& literal : orderedLiterals) {
    StateCube singleton{literal};
    if (const auto cachedCore =
            findPdrResetUnreachableCoreForCube(
                cache, singleton, postBootstrapSteps);
        cachedCore.has_value()) {
      return *cachedCore; // LCOV_EXCL_LINE
    }
    const ResetFrontierCubeKey singletonKey =
        resetFrontierCacheKey(singleton, postBootstrapSteps);
    if (const auto it = cache.outsideByCubeKey.find(singletonKey);
        it != cache.outsideByCubeKey.end()) {
      if (it->second) { // LCOV_EXCL_LINE
        return singleton;  // LCOV_EXCL_LINE
      }
      continue; // LCOV_EXCL_LINE
    }

    if (postBootstrapSteps > 0 &&
        findPdrResetUnreachableCoreForCube(
            cache, singleton, postBootstrapSteps - 1)
            .has_value()) {
      const size_t targetStep = // LCOV_EXCL_LINE
          problem.resetBootstrapCycles + postBootstrapSteps; // LCOV_EXCL_LINE
      if (const auto priorSingletonConflict = // LCOV_EXCL_LINE
              resetSpecializedConflictCubeAtStep( // LCOV_EXCL_LINE
                  problem, // LCOV_EXCL_LINE
                  transitionByState, // LCOV_EXCL_LINE
                  cache, // LCOV_EXCL_LINE
                  singleton,
                  targetStep, // LCOV_EXCL_LINE
                  frameInvariant); // LCOV_EXCL_LINE
          priorSingletonConflict.has_value() && // LCOV_EXCL_LINE
          cubeContainsCube(singleton, *priorSingletonConflict)) { // LCOV_EXCL_LINE
        cache.outsideByCubeKey.emplace(singletonKey, true); // LCOV_EXCL_LINE
        releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
            cache, problem, "prior_singleton_reset_frontier_core"); // LCOV_EXCL_LINE
        if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
          emitSecDiag( // LCOV_EXCL_LINE
              "SEC PDR stats: prior singleton reset-frontier core ",
              "cube=", cube.size(), // LCOV_EXCL_LINE
              "->", priorSingletonConflict->size(), // LCOV_EXCL_LINE
              " post_bootstrap_steps=", postBootstrapSteps,
              " hash=", cubeFingerprint(*priorSingletonConflict)); // LCOV_EXCL_LINE
        } // LCOV_EXCL_LINE
        return *priorSingletonConflict; // LCOV_EXCL_LINE
      }
    } // LCOV_EXCL_LINE

    if (freshLargeDualRailSingletonResetFrontierQueryTooDeep(
            problem, postBootstrapSteps)) {
      emitSkippedFreshLargeDualRailExactResetFrontierQuery( // LCOV_EXCL_LINE
          problem, singleton, postBootstrapSteps, // LCOV_EXCL_LINE
          "singleton_reset_frontier_core"); // LCOV_EXCL_LINE
      continue; // LCOV_EXCL_LINE
    }

    ++probes;
    releaseLargeDualRailResetFrontierContext(
        cache, problem, "before_singleton_reset_frontier_core");
    ResetFrontierReachabilityContext& reachabilityContext =
        resetReachabilityContextFor(
            cache, problem, transitionByState, frameInvariant);
    const auto assignments = cubeAssignments(singleton);
    const bool reuseSingletonResetFrontierSolver =
        mode == ConcreteCubeReachabilityMode::CachedAssumptions &&
        hasLocalDualRailFinalLeafRepairSurface(problem);
    // A singleton has no smaller failed-assumption core to recover. BP-scale
    // surfaces still use a fresh exact proof; local Swerv leaves reuse the
    // reset-prefix solver because they validate many neighboring singleton
    // roots while staying below the local rail-state guard.
    const bool reachable =
        reuseSingletonResetFrontierSolver
            ? isStateCubeReachableAtResetFrontier( // LCOV_EXCL_LINE
                  reachabilityContext, // LCOV_EXCL_LINE
                  solverType, // LCOV_EXCL_LINE
                  assignments,
                  postBootstrapSteps, // LCOV_EXCL_LINE
                  /*usePostBootstrapPrechecks=*/false)
            : isStateCubeReachableAtResetFrontierOneShot(
                  reachabilityContext,
                  solverType,
                  assignments,
                  postBootstrapSteps,
                  /*usePostBootstrapPrechecks=*/false);
    if (!reachable) {
      rememberPdrResetUnreachableCore(cache, singleton, postBootstrapSteps); // LCOV_EXCL_LINE
      rememberResetFrontierUnreachableCube( // LCOV_EXCL_LINE
          reachabilityContext, assignments, postBootstrapSteps); // LCOV_EXCL_LINE
      cache.outsideByCubeKey.emplace(singletonKey, true); // LCOV_EXCL_LINE
      releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
          cache, problem, "singleton_reset_frontier_core"); // LCOV_EXCL_LINE
      if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
        emitSecDiag( // LCOV_EXCL_LINE
            "SEC PDR stats: exact singleton reset-frontier core ",
            "cube=", cube.size(), // LCOV_EXCL_LINE
            "->1 post_bootstrap_steps=", postBootstrapSteps,
            " probes=", probes,
            " hash=", cubeFingerprint(singleton)); // LCOV_EXCL_LINE
      } // LCOV_EXCL_LINE
      return singleton; // LCOV_EXCL_LINE
    }
    cache.outsideByCubeKey.emplace(singletonKey, false);
    releaseLargeDualRailResetFrontierContext(
        cache, problem, "reachable_singleton_reset_frontier_probe");
  }
  return std::nullopt;
}

bool cubeOutsideConcreteResetFrontier(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    bool useResetConstantShortcut,
    ConcreteCubeReachabilityMode mode,
    BoolExpr* frameInvariant,
    // LCOV_EXCL_START
    bool resourceLimitStartupExactQuery) {
  if (problem.resetBootstrapCycles == 0) {
  // LCOV_EXCL_STOP
    return false;
  }
  const ResetFrontierCubeKey key =
      resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return it->second;
  }
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return true;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  bool outside = false;
  bool outsideFromExactResetFrontier = false;
  bool usedExactResetFrontierQuery = false;
  const auto knownInitIntersection =
      // LCOV_EXCL_START
      postBootstrapSteps == 0
          ? cubeIntersectsKnownInitFacts(problem, cube)
          // LCOV_EXCL_STOP
          : std::optional<bool>{};
  // LCOV_EXCL_START
  if (knownInitIntersection.has_value() && !*knownInitIntersection) {
  // LCOV_EXCL_STOP
    // Structured init/bootstrap facts are exact facts about the reset frontier.
    // If they already contradict the cube, avoid rebuilding the much heavier
    // LCOV_EXCL_START
    // reset-prefix SAT query just to rediscover that contradiction.
    // LCOV_EXCL_STOP
    outside = true;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  } else if (postBootstrapSteps == 0 &&
  // LCOV_EXCL_STOP
      useResetConstantShortcut &&
      // LCOV_EXCL_START
      (cubeContradictsResetSpecializedConstants(problem, transitionByState, cube) ||
       resetSpecializedConflictCube(
       // LCOV_EXCL_STOP
           problem, transitionByState, cache, cube).has_value())) {
    outside = true;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  } else {  // LCOV_EXCL_LINE
    if (postBootstrapSteps == 0 && pdrResetShortcutDiagEnabled()) {
    // LCOV_EXCL_STOP
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: reset-specialized exact fallback ",
          "cube=",
          cube.size(),  // LCOV_EXCL_LINE
          " use_shortcut=",
          // LCOV_EXCL_START
          useResetConstantShortcut ? "true" : "false",  // LCOV_EXCL_LINE
          " known_init=",
          knownInitIntersection.has_value()  // LCOV_EXCL_LINE
              ? (*knownInitIntersection ? "sat" : "unsat")  // LCOV_EXCL_LINE
              : "unknown",
              // LCOV_EXCL_STOP
          " hash=",
          cubeFingerprint(cube));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    releaseLargeDualRailResetFrontierContext(
        cache, problem, "before_outside_concrete_reset_frontier");
    ResetFrontierReachabilityContext& reachabilityContext =
        resetReachabilityContextFor(
            cache, problem, transitionByState, frameInvariant);
    usedExactResetFrontierQuery = true;
    const bool useExactPrechecks = useResetFrontierPostBootstrapPrechecks(
        problem,
        postBootstrapSteps,
        /*requested=*/true,
        "outside_concrete_reset_frontier");
    outside =
        mode == ConcreteCubeReachabilityMode::OneShotUnitClauses
            ? !isStateCubeReachableAtResetFrontierOneShot(  // LCOV_EXCL_LINE
                  reachabilityContext,  // LCOV_EXCL_LINE
                  solverType,  // LCOV_EXCL_LINE
                  cubeAssignments(cube),  // LCOV_EXCL_LINE
                  postBootstrapSteps,  // LCOV_EXCL_LINE
                  useExactPrechecks)  // LCOV_EXCL_LINE
            : !isStateCubeReachableAtResetFrontier(
                  reachabilityContext,
                  solverType,
                  cubeAssignments(cube),
                  postBootstrapSteps,
                  useExactPrechecks,
                  resourceLimitStartupExactQuery
                      ? kOptionalStartupResetFrontierConflictLimit
                      : -1,
                  resourceLimitStartupExactQuery
                      ? kOptionalStartupResetFrontierPropagationLimit
                      : -1);
    // LCOV_EXCL_START
    outsideFromExactResetFrontier = outside;
  }
  if (outside) {
    if (outsideFromExactResetFrontier) {
      rememberExactResetFrontierUnreachableCore(
          problem,
          solverType,
          // LCOV_EXCL_STOP
          transitionByState,
          cube,
          postBootstrapSteps,
          cache,
          frameInvariant);
    } else {
      rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
          cache,  // LCOV_EXCL_LINE
          problem,  // LCOV_EXCL_LINE
          transitionByState,  // LCOV_EXCL_LINE
          cube,  // LCOV_EXCL_LINE
          postBootstrapSteps,  // LCOV_EXCL_LINE
          frameInvariant);  // LCOV_EXCL_LINE
    }
  }
  // LCOV_EXCL_START
  cache.outsideByCubeKey.emplace(key, outside);
  if (usedExactResetFrontierQuery) {
    releaseLargeDualRailResetFrontierContext(
        cache, problem, "outside_concrete_reset_frontier");
  }
  // LCOV_EXCL_STOP
  return outside;
}

bool cubeOutsideConcreteFrameByCheapResetFacts(
    const KInductionProblem& problem,
    // LCOV_EXCL_START
    KEPLER_FORMAL::Config::SolverType solverType,
    // LCOV_EXCL_STOP
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    // LCOV_EXCL_START
    BoolExpr* frameInvariant,
    bool allowLargeDualRailSmallCubeBudget) {
  if (problem.resetBootstrapCycles == 0) {
  // LCOV_EXCL_STOP
    return false;  // LCOV_EXCL_LINE
  }
  const ResetFrontierCubeKey key =
      resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return it->second;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return true;  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_STOP

  std::optional<StateCube> conflict;
  if (postBootstrapSteps == 0) {
    const auto knownInitIntersection =
        cubeIntersectsKnownInitFacts(problem, cube);
    if (knownInitIntersection.has_value() && !*knownInitIntersection) {
      // LCOV_EXCL_START
      conflict = cube;  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    } else if (cubeContradictsResetSpecializedConstants(
                   problem, transitionByState, cube)) {
      conflict = cube;
    } else {
      conflict =  // LCOV_EXCL_LINE
          resetSpecializedConflictCube(problem, transitionByState, cache, cube);  // LCOV_EXCL_LINE
    }
  } else {
    if (const auto transitionImpossibleCore =
            // LCOV_EXCL_START
            proveTransitionImpossibleResetCoreForCube(
                problem, solverType, transitionByState, cube, cache);
                // LCOV_EXCL_STOP
        transitionImpossibleCore.has_value()) {
      conflict = *transitionImpossibleCore;  // LCOV_EXCL_LINE
    } else if (const auto previousCore =
                   findPreviousResetCoreImpliedByOneStepTransition(
                       problem,
                       solverType,
                       transitionByState,
                       cube,
                       postBootstrapSteps,
                       cache);
               previousCore.has_value()) {
      conflict = cube;  // LCOV_EXCL_LINE
    } else {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      const size_t targetStep =
      // LCOV_EXCL_STOP
          problem.resetBootstrapCycles + postBootstrapSteps;
      const bool allowRelaxedResetBudget =
          allowLargeDualRailSmallCubeBudget &&
          hasLargeDualRailResetFrontierSurface(problem) &&
          cube.size() <= kMaxDeepSmallCubeResetSymbolicLiterals;
      if (const auto priorCoreConflict =
              resetSpecializedPriorCoreConflictAtStep(
                  problem,
                  transitionByState,
                  cube,
                  postBootstrapSteps,
                  targetStep,
                  cache,
                  frameInvariant,
                  // LCOV_EXCL_START
                  allowRelaxedResetBudget);
          priorCoreConflict.has_value()) {
          // LCOV_EXCL_STOP
        conflict = *priorCoreConflict;  // LCOV_EXCL_LINE
      } else if (const auto resetConflict =
                     resetSpecializedConflictCubeAtStep(
                         problem,
                         transitionByState,
                         cache,
                         cube,
                         targetStep,
                         frameInvariant,
                         allowRelaxedResetBudget);
                 resetConflict.has_value()) {
        conflict = *resetConflict;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }
  }

  if (!conflict.has_value()) {
    return false;
  }

  rememberPdrAndResetFrontierUnreachableCore(
      cache, problem, transitionByState, *conflict, postBootstrapSteps,
      frameInvariant);
  cache.outsideByCubeKey.emplace(key, true);
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: cheap concrete-frame conflict ",
        "post_bootstrap_steps=", postBootstrapSteps,
        " cube=", cube.size(),
        "->", conflict->size(),
        " hash=", cubeFingerprint(*conflict));
    emitSecDiag(
        "SEC PDR stats: reset-specialized concrete-frame conflict ",
        "post_bootstrap_steps=", postBootstrapSteps,
        " cube=", cube.size(),
        "->", conflict->size(),
        " hash=", cubeFingerprint(*conflict));
  }
  releaseLargeDualRailResetFrontierContext(
      cache, problem, "cheap_concrete_frame_conflict");
  return true;
}

bool cubeReachableAtConcreteFrame(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode,
    BoolExpr* frameInvariant,
    bool usePostBootstrapPrechecks) {
  const ResetFrontierCubeKey key =
      resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return !it->second;
  }
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);
    return false;
  // LCOV_EXCL_START
  }

  const auto assignments = cubeAssignments(cube);
  if (problem.resetBootstrapCycles != 0) {
    if (postBootstrapSteps > 0) {
      if (const auto transitionImpossibleCore =
              proveTransitionImpossibleResetCoreForCube(
                  problem,
                  solverType,
                  // LCOV_EXCL_STOP
          transitionByState,
          cube,
          cache);
          transitionImpossibleCore.has_value()) {
        rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
            cache,  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            *transitionImpossibleCore,  // LCOV_EXCL_LINE
            postBootstrapSteps,  // LCOV_EXCL_LINE
            frameInvariant);  // LCOV_EXCL_LINE
        cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
        releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
            cache, problem, "transition_impossible_concrete_frame"); // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        return false;  // LCOV_EXCL_LINE
      }
    }

    if (const auto previousCore =
            findPreviousResetCoreImpliedByOneStepTransition(
                problem,
                solverType,
                transitionByState,
                // LCOV_EXCL_STOP
                cube,
                postBootstrapSteps,
                cache);
        previousCore.has_value()) {
      rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
          cache,  // LCOV_EXCL_LINE
          problem,  // LCOV_EXCL_LINE
          transitionByState,  // LCOV_EXCL_LINE
          cube,  // LCOV_EXCL_LINE
          postBootstrapSteps,  // LCOV_EXCL_LINE
          frameInvariant);  // LCOV_EXCL_LINE
      cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
      releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
          cache, problem, "previous_reset_core_concrete_frame"); // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }

    ResetSymbolicEvaluator& evaluator =
        resetSymbolicEvaluatorFor(cache, problem, transitionByState);
    // LCOV_EXCL_START
    evaluator.resetBudget();
    const size_t targetStep =
        problem.resetBootstrapCycles + postBootstrapSteps;
    if (const auto priorCoreConflict =
            resetSpecializedPriorCoreConflictAtStep(
                problem,
                transitionByState,
                cube,
                postBootstrapSteps,
                // LCOV_EXCL_STOP
                targetStep,
                cache,
                frameInvariant);
        priorCoreConflict.has_value()) {
      rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
          cache,  // LCOV_EXCL_LINE
          problem,  // LCOV_EXCL_LINE
          transitionByState,  // LCOV_EXCL_LINE
          *priorCoreConflict,  // LCOV_EXCL_LINE
          postBootstrapSteps,  // LCOV_EXCL_LINE
          frameInvariant);  // LCOV_EXCL_LINE
      cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
      releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
          cache, problem, "prior_reset_core_concrete_frame"); // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    if (const auto conflict =
            resetSpecializedConflictCubeAtStep(
            // LCOV_EXCL_STOP
                problem,
                transitionByState,
                cache,
                cube,
                // LCOV_EXCL_START
                targetStep,
                // LCOV_EXCL_STOP
                frameInvariant);
        // LCOV_EXCL_START
        conflict.has_value()) {
        // LCOV_EXCL_STOP
      // This is the same reset-image proof used for F[0] refinement, evaluated
      // LCOV_EXCL_START
      // at a later post-reset frame.  Missing transitions remain free
      // variables, so a conflict here is a sound concrete-unreachability fact
      // LCOV_EXCL_STOP
      // and avoids the wide bounded SAT unroll sampled on AES.
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: reset-specialized concrete-frame conflict ",
            "post_bootstrap_steps=",
            // LCOV_EXCL_START
            postBootstrapSteps,
            " cube=",
            cube.size(),  // LCOV_EXCL_LINE
            "->",
            conflict->size(),  // LCOV_EXCL_LINE
            " hash=",
            cubeFingerprint(*conflict));  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      // The reset-specialized proof is an exact reset-image conflict, just
      // LCOV_EXCL_STOP
      // cheaper than opening the bounded reset-frontier SAT query. Feed it into
      // the lightweight PDR reset-core cache so the next post-bootstrap check
      // can reuse the fact without first constructing the broad reset-frontier
      // SAT context sampled on BlackParrot.
      rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
          cache,  // LCOV_EXCL_LINE
          problem,  // LCOV_EXCL_LINE
          transitionByState,  // LCOV_EXCL_LINE
          *conflict,  // LCOV_EXCL_LINE
          postBootstrapSteps,  // LCOV_EXCL_LINE
          frameInvariant);  // LCOV_EXCL_LINE
      cache.outsideByCubeKey.emplace(key, true);  // LCOV_EXCL_LINE
      releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
          cache, problem, "reset_specialized_concrete_frame"); // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
  }
  if (const auto singletonCore =
          proveLargeDualRailSingletonResetFrontierCore(
              problem,
              solverType,
              transitionByState,
              cube,
              postBootstrapSteps,
              cache,
              mode,
              frameInvariant);
      singletonCore.has_value()) {
    rememberPdrAndResetFrontierUnreachableCore( // LCOV_EXCL_LINE
        cache, // LCOV_EXCL_LINE
        problem, // LCOV_EXCL_LINE
        transitionByState, // LCOV_EXCL_LINE
        *singletonCore, // LCOV_EXCL_LINE
        postBootstrapSteps, // LCOV_EXCL_LINE
        frameInvariant); // LCOV_EXCL_LINE
    cache.outsideByCubeKey.emplace(key, true); // LCOV_EXCL_LINE
    return false; // LCOV_EXCL_LINE
  }
  if (freshLargeDualRailExactResetFrontierQueryTooDeep(
          problem, postBootstrapSteps)) {
    emitSkippedFreshLargeDualRailExactResetFrontierQuery( // LCOV_EXCL_LINE
        problem, cube, postBootstrapSteps, "concrete_frame_reachability"); // LCOV_EXCL_LINE
    releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
        cache, problem, "skipped_deep_exact_reset_frontier"); // LCOV_EXCL_LINE
    markPdrBudgetExhausted(PdrBudgetExhaustion::LocalQuery); // LCOV_EXCL_LINE
    return true; // LCOV_EXCL_LINE
  }
  releaseLargeDualRailResetFrontierContext(
      cache, problem, "before_concrete_frame_reachability");
  ResetFrontierReachabilityContext& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  const bool useExactPrechecks = useResetFrontierPostBootstrapPrechecks(
      problem,
      postBootstrapSteps,
      usePostBootstrapPrechecks,
      "concrete_frame_reachability");
  const bool reachable =
      mode == ConcreteCubeReachabilityMode::OneShotUnitClauses
          ? isStateCubeReachableAtResetFrontierOneShot(
                reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps,
                useExactPrechecks)
          : isStateCubeReachableAtResetFrontier(
                reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps,
                useExactPrechecks);
  if (!reachable) {
    rememberExactResetFrontierUnreachableCore(
        problem,
        solverType,
        transitionByState,
        cube,
        postBootstrapSteps,
        cache,
        frameInvariant);
  }
  cache.outsideByCubeKey.emplace(key, !reachable);
  releaseLargeDualRailResetFrontierContext(
      cache, problem, "concrete_frame_reachability");
  return reachable;
}

bool cubeReachableWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    ConcreteCubeReachabilityMode mode,
    BoolExpr* frameInvariant) {
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: concrete cube reachability begin ",
        "cube=", cube.size(),
        " max_step=", maxPostBootstrapSteps,
        " mode=", concreteCubeReachabilityModeName(mode));
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  bool everyStepKnownOutside = true;
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const auto it = cache.outsideByCubeKey.find(resetFrontierCacheKey(cube, step));
    if (it == cache.outsideByCubeKey.end()) {
      everyStepKnownOutside = false;
      continue;
    }
    if (!it->second) {
      return true;
    }
  }
  if (everyStepKnownOutside) {
    return false;  // LCOV_EXCL_LINE
  }
  if (problem.resetBootstrapCycles != 0) {
    bool everyStepCheaplyOutside = true;
    std::vector<size_t> remainingExactSteps;
    for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
      if (!cubeOutsideConcreteFrameByCheapResetFacts(
              problem,
              solverType,
              transitionByState,
              cube,
              step,
              cache,
              frameInvariant,
              /*allowLargeDualRailSmallCubeBudget=*/true)) {
        // LCOV_EXCL_START
        everyStepCheaplyOutside = false;
        remainingExactSteps.push_back(step);
        // LCOV_EXCL_STOP
        continue;
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      if (pdrStatsEnabled()) {
        // LCOV_EXCL_START
        emitSecDiag(
            "SEC PDR stats: concrete cube reachability step ",
            // LCOV_EXCL_STOP
            "step=", step,
            " result=unsat",
            " mode=", concreteCubeReachabilityModeName(mode));
      }
    }
    if (everyStepCheaplyOutside) {
      if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: concrete cube reachability cheap reset proof ",
            "cube=", cube.size(),  // LCOV_EXCL_LINE
            " max_step=", maxPostBootstrapSteps);
      }  // LCOV_EXCL_LINE
      return false;  // LCOV_EXCL_LINE
    }
    if (remainingExactSteps.size() <=
        kMaxSparseConcreteReachabilityPerFrameChecks) {
      for (const auto step : remainingExactSteps) {
        // Preserve the caller-selected validation mode.  Large dual-rail roots
        // need cached assumptions so neighboring cubes reuse the reset-prefix
        // solver instead of rebuilding it once per sparse frame.
        const bool reachable = cubeReachableAtConcreteFrame(
            problem,
            solverType,
            transitionByState,
            cube,
            step,
            cache,
            // LCOV_EXCL_START
            mode,
            // LCOV_EXCL_STOP
            frameInvariant);
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: concrete cube reachability sparse step ",
              "step=", step,
              " result=", reachable ? "sat" : "unsat",
              // LCOV_EXCL_START
              " mode=", concreteCubeReachabilityModeName(mode));
        }
        if (reachable) {
          return true;
        }
      }
      return false;
    }
  }
  const bool preferPerFrameValidation =
      maxPostBootstrapSteps <= kMaxPerFrameConcreteValidationDepth &&
      cube.size() <= kMaxPerFrameConcreteValidationCubeLiterals;
  if (problem.resetBootstrapCycles != 0 &&
      maxPostBootstrapSteps >= kSharedPrefixConcreteValidationMinDepth &&
      !preferPerFrameValidation) {  // LCOV_EXCL_LINE
    ResetFrontierReachabilityContext& reachabilityContext =  // LCOV_EXCL_LINE
        resetReachabilityContextFor(  // LCOV_EXCL_LINE
            cache, problem, transitionByState, frameInvariant);  // LCOV_EXCL_LINE
    const bool reachable = isStateCubeReachableWithinResetFrontier(  // LCOV_EXCL_LINE
        reachabilityContext,  // LCOV_EXCL_LINE
        solverType,  // LCOV_EXCL_LINE
        cubeAssignments(cube),  // LCOV_EXCL_LINE
        maxPostBootstrapSteps);  // LCOV_EXCL_LINE
    if (!reachable) {  // LCOV_EXCL_LINE
      const auto assignments = cubeAssignments(cube);  // LCOV_EXCL_LINE
      for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {  // LCOV_EXCL_LINE
        cache.outsideByCubeKey.emplace(resetFrontierCacheKey(cube, step), true);  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
        const auto core = SEC::findResetFrontierUnreachableCubeCore(  // LCOV_EXCL_LINE
            reachabilityContext, solverType, assignments, step);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        rememberPdrAndResetFrontierUnreachableCore(  // LCOV_EXCL_LINE
            cache,  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            transitionByState,  // LCOV_EXCL_LINE
            core.has_value() ? cubeFromAssignments(*core) : cube,  // LCOV_EXCL_LINE
            step,  // LCOV_EXCL_LINE
            frameInvariant);  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: concrete cube reachability shared-prefix ",
          "max_step=", maxPostBootstrapSteps,
          " result=", reachable ? "sat" : "unsat");  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
        cache, problem, "shared_prefix_concrete_reachability"); // LCOV_EXCL_LINE
    return reachable;  // LCOV_EXCL_LINE
  }
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const bool reachable = cubeReachableAtConcreteFrame(
            problem,
            solverType,
            transitionByState,
            cube,
            step,
            cache,
            mode,
            frameInvariant);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: concrete cube reachability step ",
          "step=", step,
          " result=", reachable ? "sat" : "unsat",
          " mode=", concreteCubeReachabilityModeName(mode));
    }
    if (reachable) {
      return true;
    }
  // LCOV_EXCL_START
  }
  // LCOV_EXCL_STOP
  return false;
}

// LCOV_EXCL_START
std::optional<StateCube> boundedResetFrontierCoreWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (problem.resetBootstrapCycles == 0 ||
  // LCOV_EXCL_STOP
      maxPostBootstrapSteps < kSharedPrefixConcreteValidationMinDepth) {  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return std::nullopt;
  }


// LCOV_EXCL_STOP
  ResetFrontierReachabilityContext& reachabilityContext =  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
          // LCOV_EXCL_STOP
  const auto assignments = cubeAssignments(cube);  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  StateCube unionCore;
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const auto core = findResetFrontierUnreachableCubeCore(
        reachabilityContext,
        // LCOV_EXCL_STOP
        solverType,  // LCOV_EXCL_LINE
        assignments,
        step);  // LCOV_EXCL_LINE
    if (!core.has_value()) {  // LCOV_EXCL_LINE
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    for (const auto& [symbol, value] : *core) {
      unionCore.push_back({symbol, value});
    }
  }
  // LCOV_EXCL_STOP
  normalizeCube(unionCore);  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  if (unionCore.empty() || unionCore.size() >= cube.size()) {
    return std::nullopt;
    // LCOV_EXCL_STOP
  }

// LCOV_EXCL_START

  // Each per-frame failed-assumption core proves that core unreachable only at
  // LCOV_EXCL_STOP
  // its own frame. Their union is stronger than every per-frame core, so it is
  // LCOV_EXCL_START
  // unreachable at all frames; this final cached check records that fact in the
  // PDR reset cache and guards against backends that return non-core fallbacks.
  // LCOV_EXCL_STOP
  if (cubeReachableWithinConcreteFrames(  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          problem,  // LCOV_EXCL_LINE
          solverType,  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          transitionByState,  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          unionCore,
          maxPostBootstrapSteps,  // LCOV_EXCL_LINE
          cache,  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          ConcreteCubeReachabilityMode::CachedAssumptions,
          frameInvariant)) {  // LCOV_EXCL_LINE
    releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
        cache, problem, "bounded_reset_frontier_core"); // LCOV_EXCL_LINE
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: bounded reset-frontier core ",
        "cube=", cube.size(),  // LCOV_EXCL_LINE
        "->", unionCore.size(),  // LCOV_EXCL_LINE
        " max_step=", maxPostBootstrapSteps,
        " hash=", cubeFingerprint(unionCore));  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  }  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
      cache, problem, "bounded_reset_frontier_core"); // LCOV_EXCL_LINE
  return unionCore;  // LCOV_EXCL_LINE
}

std::optional<StateCube> cachedResetCoreWithinConcreteFrames(
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    const ResetFrontierCache& cache) {
  // LCOV_EXCL_START
  StateCube unionCore;
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
  // LCOV_EXCL_STOP
    const auto core =
        // LCOV_EXCL_START
        findPdrResetUnreachableCoreForCube(cache, cube, step);
    if (!core.has_value()) {
    // LCOV_EXCL_STOP
      return std::nullopt;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }
    unionCore.insert(unionCore.end(), core->begin(), core->end());
  }
  // LCOV_EXCL_STOP
  normalizeCube(unionCore);
  if (unionCore.empty() || unionCore.size() >= cube.size()) {
    // LCOV_EXCL_START
    return std::nullopt;
    // LCOV_EXCL_STOP
  }
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: cached bounded reset core ",
        "cube=", cube.size(),  // LCOV_EXCL_LINE
        "->", unionCore.size(),  // LCOV_EXCL_LINE
        " max_step=", maxPostBootstrapSteps,
        " hash=", cubeFingerprint(unionCore));  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return unionCore;  // LCOV_EXCL_LINE
// LCOV_EXCL_START
}

StateCube generalizeResetFrontierCube(  // LCOV_EXCL_LINE
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    ResetFrontierCache& cache,
    // LCOV_EXCL_STOP
    BoolExpr* frameInvariant) {
  // LCOV_EXCL_START
  // This is an exact, reset-specific literal dropping pass. A reduced cube is
  // accepted only when the concrete reset-frontier SAT query proves that no
  // real post-reset state can satisfy it. The resulting F[0] clause is thus a
  // stronger abstraction refinement, not a heuristic shortcut.
  // LCOV_EXCL_STOP
  StateCube candidate = cube;  // LCOV_EXCL_LINE
  // LCOV_EXCL_START
  ResetFrontierReachabilityContext& reachabilityContext =  // LCOV_EXCL_LINE
      resetReachabilityContextFor(  // LCOV_EXCL_LINE
          cache, problem, transitionByState, frameInvariant);  // LCOV_EXCL_LINE
  if (const auto core = findResetFrontierUnreachableCubeCore(  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
          reachabilityContext,  // LCOV_EXCL_LINE
          solverType,  // LCOV_EXCL_LINE
          cubeAssignments(candidate),  // LCOV_EXCL_LINE
          0);
      // LCOV_EXCL_START
      core.has_value() && core->size() < candidate.size()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
    candidate = cubeFromAssignments(*core);  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: reset-frontier core ",
          "cube=", cube.size(),  // LCOV_EXCL_LINE
          "->", candidate.size(),  // LCOV_EXCL_LINE
          " hash=", cubeFingerprint(candidate));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    // The failed-assumption core is already an exact unreachable reset-frontier
    // cube.  Do not spend additional SAT calls trying to minimize it further:
    // on AES this optional 2->1 literal probing rebuilt the same 956-symbol
    // reset solver and dominated the PDR regression.
    // LCOV_EXCL_STOP
    releaseLargeDualRailResetFrontierContext( // LCOV_EXCL_LINE
        cache, problem, "reset_frontier_generalization_core"); // LCOV_EXCL_LINE
    return candidate;  // LCOV_EXCL_LINE
  }
  // LCOV_EXCL_START
  size_t index = 0;  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  size_t attempts = 0;  // LCOV_EXCL_LINE
  while (index < candidate.size() &&  // LCOV_EXCL_LINE
         // LCOV_EXCL_START
         attempts < kMaxResetFrontierGeneralizationAttempts) {  // LCOV_EXCL_LINE
         // LCOV_EXCL_STOP
    ++attempts;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    StateCube reduced = candidate;  // LCOV_EXCL_LINE
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    if (cubeOutsideConcreteResetFrontier(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            reduced,
            // LCOV_EXCL_STOP
            0,
            // LCOV_EXCL_START
            cache,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            true,
            ConcreteCubeReachabilityMode::CachedAssumptions,
            frameInvariant,  // LCOV_EXCL_LINE
            /*resourceLimitStartupExactQuery=*/true)) {
      candidate = std::move(reduced);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    // LCOV_EXCL_START
    ++index;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  releaseLargeDualRailResetFrontierContext(
      cache, problem, "reset_frontier_generalization");
  return candidate;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

StateCube generalizeInitExcludedCube(const KInductionProblem& problem,  // LCOV_EXCL_LINE
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     const StateCube& cube) {
  // Ordinary Init can also be a relational frontier made of equality facts.
  // When a projected predecessor violates that frontier, learn a generalized
  // LCOV_EXCL_STOP
  // F[0] clause immediately instead of relying on many small seed clauses to
  // LCOV_EXCL_START
  // rediscover adjacent impossible cubes one at a time.
  StateCube candidate = cube;  // LCOV_EXCL_LINE
  size_t index = 0;  // LCOV_EXCL_LINE
  size_t attempts = 0;  // LCOV_EXCL_LINE
  // LCOV_EXCL_STOP
  while (index < candidate.size() &&  // LCOV_EXCL_LINE
         attempts < kMaxResetFrontierGeneralizationAttempts) {  // LCOV_EXCL_LINE
    ++attempts;  // LCOV_EXCL_LINE
    StateCube reduced = candidate;  // LCOV_EXCL_LINE
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));  // LCOV_EXCL_LINE
    if (!cubeIntersectsInit(problem, solverType, initFormula, reduced)) {  // LCOV_EXCL_LINE
      candidate = std::move(reduced);  // LCOV_EXCL_LINE
      continue;  // LCOV_EXCL_LINE
    }
    ++index;  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  return candidate;  // LCOV_EXCL_LINE
}  // LCOV_EXCL_LINE

StateCube generalizeBoundedUnreachableRootCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    // LCOV_EXCL_START
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    // LCOV_EXCL_STOP
    BoolExpr* frameInvariant,
    size_t maxAttempts,
    size_t& attempts) {
  // Every literal drop is checked against the concrete bounded transition
  // LCOV_EXCL_START
  // prefix, so the learned clause remains a real CEGAR refinement of the
  // projected PDR trace rather than a heuristic pruning trick.
  // LCOV_EXCL_STOP
  StateCube candidate = cube;
  if (const auto cachedCore =
          cachedResetCoreWithinConcreteFrames(
              cube, maxPostBootstrapSteps, cache);
      cachedCore.has_value()) {
    attempts = 0;  // LCOV_EXCL_LINE
    return *cachedCore;  // LCOV_EXCL_LINE
  }
  if (maxPostBootstrapSteps > kMaxDepthForBoundedRootGeneralization &&
      transitionByState.stateSymbols().size() >=
          // LCOV_EXCL_START
          kMinStateSymbolsForDeepRootGeneralizationBypass) {
    attempts = 0;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
    return candidate;  // LCOV_EXCL_LINE
  }
  if (const auto resetCore = boundedResetFrontierCoreWithinConcreteFrames(
          problem,
          solverType,
          transitionByState,
          cube,
          maxPostBootstrapSteps,
          cache,
          // LCOV_EXCL_START
          frameInvariant);
          // LCOV_EXCL_STOP
      resetCore.has_value()) {
    attempts = 0;  // LCOV_EXCL_LINE
    return *resetCore;  // LCOV_EXCL_LINE
  }
  size_t index = 0;
  attempts = 0;
  while (index < candidate.size() && attempts < maxAttempts) {
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (reduced.empty()) {
      // The empty cube is the whole state space, so it cannot be a useful
      // unreachable-root generalization.  Avoid a concrete reachability query
      // that only proves that trivial fact after rebuilding the reset prefix.
      ++index;
      continue;
    }
    ++attempts;
    const bool preferShallowPerFrameValidation =
        maxPostBootstrapSteps <= kMaxPerFrameConcreteValidationDepth &&
        reduced.size() <= kMaxPerFrameConcreteValidationCubeLiterals;  // LCOV_EXCL_LINE
    if (!cubeReachableWithinConcreteFrames(
            problem,
            solverType,
            transitionByState,
            reduced,
            maxPostBootstrapSteps,
            cache,
            preferShallowPerFrameValidation
                ? ConcreteCubeReachabilityMode::OneShotUnitClauses
                : ConcreteCubeReachabilityMode::CachedAssumptions,
            frameInvariant)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

bool proofObligationLess(const ProofObligation& lhs, const ProofObligation& rhs) {
  if (lhs.level != rhs.level) {
    return lhs.level < rhs.level;
  }
  if (lhs.cube.size() != rhs.cube.size()) {
    return lhs.cube.size() < rhs.cube.size();
  }
  if (lhs.badFrame != rhs.badFrame) {
    return lhs.badFrame < rhs.badFrame; // LCOV_EXCL_LINE
  }
  if (stateCubeLess(lhs.cube, rhs.cube)) {
    return true;
  }
  if (stateCubeLess(rhs.cube, lhs.cube)) {
    return false;
  }
  return stateCubeLess(lhs.rootCube, rhs.rootCube); // LCOV_EXCL_LINE
}

size_t popNextObligationIndex(const std::vector<ProofObligation>& queue) {
  size_t bestIndex = 0;
  for (size_t i = 1; i < queue.size(); ++i) {
    if (proofObligationLess(queue[i], queue[bestIndex])) {
      bestIndex = i;
    }
  }
  return bestIndex;
}

ProofObligationKey proofObligationKey(const ProofObligation& obligation) {
  ProofObligationKey key;
  key.level = obligation.level;
  key.badFrame = obligation.badFrame;
  key.cube = obligation.cube;
  key.rootCube = obligation.rootCube;
  return key;
// LCOV_EXCL_START
}
// LCOV_EXCL_STOP

void enqueueProofObligation(std::vector<ProofObligation>& queue,
                            std::unordered_set<
                                ProofObligationKey,
                                ProofObligationKeyHash>& queuedKeys,
                            ProofObligation obligation) {
  // Large SEC output cones can reach the same normalized cube/level pair
  // through several predecessor projections before a learned frame clause
  // subsumes it. Keep only one pending copy: once that obligation is blocked
  // or reaches Init, every duplicate would repeat the same SAT work.
  const ProofObligationKey key = proofObligationKey(obligation);
  if (!queuedKeys.insert(key).second) {
    return;  // LCOV_EXCL_LINE
  }
  queue.push_back(std::move(obligation));
}

size_t predecessorProjectionLimitForObligation(size_t /*obligationLevel*/,
                                               size_t predecessorProjectionLimit) {
  // Keep predecessor cubes under the projection budget chosen by the SEC stage.
  // A previous near-init widening helped small examples, but BlackParrot
  // sampling showed it expanding level-2 targets into 100+ literal
  // predecessors that the F[0] blocking loop could not shrink usefully.
  return predecessorProjectionLimit;
}

bool blockProofObligations(const KInductionProblem& problem,
                           KEPLER_FORMAL::Config::SolverType solverType,
                           const TransitionExprResolver& transitionByState,
                           BoolExpr* initFormula,
                           BoolExpr* frameInvariant,
                           std::vector<FrameClauses>& frames,
                           const InitFactIndex& initFacts,
                           const StateCube& rootCube,
                           size_t rootLevel,
                           size_t& badFrame,
                           const ComplementPartnerIndex& complementPartners,
                           size_t predecessorProjectionLimit,
                           bool exactFrameClauses,
                           bool refineProjectedCounterexamples,
                           ResetFrontierCache& resetFrontierCache,
                           PredecessorAssumptionCache& predecessorAssumptionCache,
                           size_t maxBoundedRootGeneralizationAttempts,
                           bool learnValidatedBadFormulaClausesOnReject,
                           bool useExactResetFrontierChecks,
                           size_t* predecessorQueryBudget,
                           size_t* projectedCounterexampleRefinementBudget,
                           PdrFormulaSupportCache* supportCache) {
  // This is the paper's recursive blocking idea expressed as an explicit queue
  // so we do not depend on deep recursion for large obligation stacks.
  std::vector<ProofObligation> queue;
  std::unordered_set<ProofObligationKey, ProofObligationKeyHash> queuedKeys;
  enqueueProofObligation(
      queue, queuedKeys, ProofObligation{rootCube, rootLevel, rootLevel, rootCube});
  bool expandedBadFormulaObligations = false;
  if (learnValidatedBadFormulaClausesOnReject &&
      problem.observedOutputExprs0.size() == 1 &&
      rootLevel > 0) {  // LCOV_EXCL_LINE
    auto badClauses = observedOutputBadFormulaClauses(  // LCOV_EXCL_LINE
        problem, transitionByState.stateSymbols());  // LCOV_EXCL_LINE
    if (!badClauses.has_value()) {  // LCOV_EXCL_LINE
      badClauses =  // LCOV_EXCL_LINE
          stateOnlyBadFormulaClauses(  // LCOV_EXCL_LINE
              problem.bad,
              transitionByState.stateSymbols(),
              validatedBadFormulaCnfSupportLimit(problem));  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (badClauses.has_value() &&  // LCOV_EXCL_LINE
        badClauses->size() > kMaxExactValidatedBadFormulaClauses &&  // LCOV_EXCL_LINE
        badClauses->size() <= singleOutputBadFormulaClauseLimit(problem)) {  // LCOV_EXCL_LINE
      size_t seededObligations = 0;  // LCOV_EXCL_LINE
      for (const auto& clause : *badClauses) {  // LCOV_EXCL_LINE
        const StateCube badCube = cubeForbiddenByStateClause(clause);  // LCOV_EXCL_LINE
        enqueueProofObligation(  // LCOV_EXCL_LINE
            queue,
            queuedKeys,
            ProofObligation{badCube, rootLevel, rootLevel, badCube});  // LCOV_EXCL_LINE
        ++seededObligations;  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
      expandedBadFormulaObligations = seededObligations != 0;  // LCOV_EXCL_LINE
      if (expandedBadFormulaObligations && pdrStatsEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC PDR stats: expanded state-only bad formula into "
            "PDR obligations ",
            "bad_frame=", rootLevel,
            " obligations=", seededObligations);
      }  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  auto learnBlockedObligation = [&](const ProofObligation& blockedObligation,
                                    bool exactClausesForGeneralization) {
    const StateCube generalizedCube = generalizeBlockedCube(
        problem,
        solverType,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        blockedObligation.level,
        blockedObligation.cube,
        &resetFrontierCache,
        &predecessorAssumptionCache,
        complementPartners,
        predecessorProjectionLimit,
        exactClausesForGeneralization,
        useExactResetFrontierChecks,
        predecessorQueryBudget,
        supportCache);
    addClauseToFrames(
        frames, clauseFromCube(generalizedCube), blockedObligation.level);
    learnExactResetPredecessorSingletonClauses(
        frames,
        resetFrontierCache,
        blockedObligation.cube,
        blockedObligation.level);
    if (blockedObligation.level < blockedObligation.badFrame) {
      const StateCube propagatedRoot =
          blockedObligation.rootCube.empty()
              ? generalizedCube
              : blockedObligation.rootCube;
      // The pushed obligation is the generalized blocked cube, but any
      // concrete counterexample must still be validated against the original
      // bad/root cube. A generalized cube is a larger state set and may be
      // reachable even when the property cube that caused it is not.
      enqueueProofObligation(
          queue,
          queuedKeys,
          ProofObligation{
              generalizedCube,
              blockedObligation.level + 1,
              blockedObligation.badFrame,
              propagatedRoot});
    // LCOV_EXCL_START
    }
  };
  auto learnBlockedObligationVerbatim =
      [&](const ProofObligation& blockedObligation) {
    // The projected-frame CEGAR loop below can prove a cube blocked only after
    // adding a few missing learned-frame clauses to that local query. Those
    // clauses are real frame facts, so learning the original cube is sound; we
    // intentionally skip optional literal-dropping here because re-running
    // generalization without the same local CEGAR blockers can rediscover the
    // LCOV_EXCL_STOP
    // stale predecessor that we just eliminated.
    addClauseToFrames(
        frames, clauseFromCube(blockedObligation.cube), blockedObligation.level);
    learnExactResetPredecessorSingletonClauses(
        frames,
        resetFrontierCache,
        blockedObligation.cube,
        blockedObligation.level);
    if (blockedObligation.level < blockedObligation.badFrame) {
      enqueueProofObligation(  // LCOV_EXCL_LINE
          queue,  // LCOV_EXCL_LINE
          queuedKeys,  // LCOV_EXCL_LINE
          ProofObligation{  // LCOV_EXCL_LINE
              blockedObligation.cube,  // LCOV_EXCL_LINE
              blockedObligation.level + 1,  // LCOV_EXCL_LINE
              blockedObligation.badFrame,  // LCOV_EXCL_LINE
              blockedObligation.rootCube});  // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
  };
  // Validated bad-formula learning is an exact repair for final SEC leaves:
  // concrete BMC validates the bad predicate and learns its state-only CNF.
  // Keep it eager for small state surfaces, and also for already-split
  // single-output leaves. AES samples showed those leaves otherwise spend
  // minutes proving a tiny root cube through the broad reset image, while the
  // bad-formula validator uses the localized proof-only base-case profile.
  const bool useObservationFrontier =
      problem.usesResetBootstrapObservationFrontier();
  const bool usePredecessorResetFrontierChecks =
      useExactResetFrontierChecks && !useObservationFrontier;
  // The exact root reset-frontier check refines an abstract level-0
  // predecessor cube before final validation. When predecessor projection is
  // disabled, sampled AES runs showed that query duplicating the following
  // concrete root-cube validation as a much harder wide reset-image SAT call.
  // Keep cheap reset-specialized facts below, but let the unprojected final
  // stage validate/refine the original root cube directly.
  const bool skipRootResetFrontierForBadFormulaRepair =
      refineProjectedCounterexamples &&
      learnValidatedBadFormulaClausesOnReject &&
      problem.observedOutputExprs0.size() == 1 &&
      expandedBadFormulaObligations;  // LCOV_EXCL_LINE
  const bool useRootResetFrontierChecks =
      useExactResetFrontierChecks && predecessorProjectionLimit != 0 &&
      !useObservationFrontier && !skipRootResetFrontierForBadFormulaRepair;
  const bool useCheapRootResetFrontierFacts =
      refineProjectedCounterexamples && problem.resetBootstrapCycles != 0;

  const bool useSingleOutputValidatedBadFormulaRepair =
      learnValidatedBadFormulaClausesOnReject &&
      problem.observedOutputExprs0.size() == 1;
  // A dual-rail batch ORs many rail-expanded output predicates together.  Keep
  // the exact bad-formula repair local to small per-output groups; large
  // multi-output rail batches must split instead of running one broad BMC.
  const bool useWholeBatchValidatedBadFormulaRepair =
      learnValidatedBadFormulaClausesOnReject &&
      exactFrameClauses &&
      !problem.usesDualRailStateEncoding &&
      problem.observedOutputExprs0.size() > 1;  // LCOV_EXCL_LINE
  const bool usePerOutputValidatedBadFormulaRepair =
      learnValidatedBadFormulaClausesOnReject &&
      !useWholeBatchValidatedBadFormulaRepair &&
      problem.observedOutputExprs0.size() > 1 &&
      problem.observedOutputExprs0.size() <=
          kMaxPerOutputValidatedBadFormulaRepairOutputs;
  const bool useEagerBadFormulaValidation =
      useSingleOutputValidatedBadFormulaRepair ||
      useWholeBatchValidatedBadFormulaRepair ||
      usePerOutputValidatedBadFormulaRepair ||
      (!expandedBadFormulaObligations &&
       // LCOV_EXCL_START
       transitionByState.stateSymbols().size() <=
       // LCOV_EXCL_STOP
           kMaxDeepEagerBadFormulaStateSymbols);
  // LCOV_EXCL_START
  const bool allowEagerBadFormulaValidationAtRoot =
      problem.resetBootstrapCycles == 0 ||
      // LCOV_EXCL_STOP
      rootLevel == 1 ||
      expandedBadFormulaObligations ||
      // LCOV_EXCL_START
      useWholeBatchValidatedBadFormulaRepair ||
      usePerOutputValidatedBadFormulaRepair;
  if (refineProjectedCounterexamples &&
      problem.observedOutputExprs0.size() > 1 &&
      !usePerOutputValidatedBadFormulaRepair &&
      // LCOV_EXCL_STOP
      !useWholeBatchValidatedBadFormulaRepair &&  // LCOV_EXCL_LINE
      rootLevel > kMaxMultiOutputProjectedRootValidationFrame &&  // LCOV_EXCL_LINE
      transitionByState.stateSymbols().size() >=  // LCOV_EXCL_LINE
          kMinStateSymbolsForDeepRootGeneralizationBypass) {
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: deferred multi-output root bad-formula repair ",
          "bad_frame=", rootLevel,
          " outputs=", problem.observedOutputExprs0.size(),  // LCOV_EXCL_LINE
          " root_cube=", rootCube.size());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    badFrame = rootLevel;  // LCOV_EXCL_LINE
    return false;  // LCOV_EXCL_LINE
  }
  if (learnValidatedBadFormulaClausesOnReject &&
      useEagerBadFormulaValidation &&
      allowEagerBadFormulaValidationAtRoot) {
    // Final SEC/PDR slices often rediscover every satisfying assignment of a
    // small output-bad predicate as separate bad cubes. For small state
    // surfaces, validate the exact bad-formula repair before walking
    // predecessors. For ASIC-size slices, sampled AES runs showed this BMC was
    // the runtime wall even at the root frontier, so normal PDR blocking gets
    // the first chance to learn local clauses.
    if (const auto refinement = learnValidatedBadFormulaClauses(
            problem,
            solverType,
            transitionByState,
            frameInvariant,
            frames,
            rootLevel,
            badFrame,
            resetFrontierCache,
            useWholeBatchValidatedBadFormulaRepair);
        refinement.has_value()) {
      return *refinement;
    }
  }  // LCOV_EXCL_LINE

  while (!queue.empty()) {
    const size_t obligationIndex = popNextObligationIndex(queue);
    const ProofObligation obligation = queue[obligationIndex];
    queuedKeys.erase(proofObligationKey(obligation));
    queue.erase(queue.begin() + static_cast<std::ptrdiff_t>(obligationIndex));
    const bool obligationExactFrameClauses = exactFrameClauses;

    if (obligationAlreadyBlocked(frames, obligation)) {
      continue;  // LCOV_EXCL_LINE
    }

    if (obligation.level == 0) {
      if (useCheapRootResetFrontierFacts) {
        if (const auto resetConflict =
                resetSpecializedConflictCube(
                    problem, transitionByState, resetFrontierCache, obligation.cube);
            resetConflict.has_value()) {
          // Final SEC/PDR stages may disable deeper exact reset-frontier SAT
          // because sampled ASIC runs showed those prefix queries dominating
          // runtime.  Still keep the zero-SAT part of reset reasoning: if
          // reset specialization directly proves a level-0 cube contradicts a
          // concrete post-reset constant/equality/complement, learning that
          // F[0] blocker is exact and avoids falling through to a wide
          // reset-image SAT query.
          addClauseToFrame(frames[0], clauseFromCube(*resetConflict));
          continue;
        }
      }
      const bool outsideConcreteResetFrontier =
          useRootResetFrontierChecks &&
          cubeOutsideConcreteResetFrontier(
              problem,
              solverType,
              transitionByState,
              obligation.cube,
              0,
              resetFrontierCache,
              true,
              // LCOV_EXCL_START
              ConcreteCubeReachabilityMode::CachedAssumptions,
              frameInvariant,
              /*resourceLimitStartupExactQuery=*/true);
      if (outsideConcreteResetFrontier) {
        // For reset-bootstrap SEC, F[0] is an over-approximation of the
        // concrete post-reset image. Reaching an abstract-only level-0 cube is
        // not a counterexample; it is a refinement opportunity. Adding the
        // negated cube to F[0] is safe because either reset-specialized
        // constants or the exact reset-image query proved that no concrete
        // post-reset state satisfies the cube. Final SEC leaves also use the
        // LCOV_EXCL_STOP
        // bad-formula repair below, so this path should stay a narrow F[0]
        // LCOV_EXCL_START
        // refinement and not become the only way we learn repeated output-bad
        // LCOV_EXCL_STOP
        // assignments.
        const StateCube generalizedCube = generalizeResetFrontierCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            obligation.cube,  // LCOV_EXCL_LINE
            resetFrontierCache,  // LCOV_EXCL_LINE
            frameInvariant);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        addClauseToFrame(  // LCOV_EXCL_LINE
            frames[0],  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            clauseFromCube(generalizedCube));  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        continue;
      }  // LCOV_EXCL_LINE
      if (const auto conflictCube =
              knownInitConflictCube(initFacts, obligation.cube);
          conflictCube.has_value()) {
        // Ordinary relational Init has the same refinement opportunity as the
        // reset-frontier path.  When the cube visibly contradicts a structured
        // LCOV_EXCL_STOP
        // init fact, learn only that conflict instead of a wide SAT-model cube;
        // this keeps large ASIC output slices from rediscovering the same
        // LCOV_EXCL_START
        // state equality violation thousands of times.
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: known init conflict ",
              "cube=", obligation.cube.size(),  // LCOV_EXCL_LINE
              " core=", conflictCube->size(),  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
              " bad_frame=", obligation.badFrame,  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              " hash=", cubeFingerprint(*conflictCube));  // LCOV_EXCL_LINE
              // LCOV_EXCL_STOP
        }  // LCOV_EXCL_LINE
        addClauseToFrame(frames[0], clauseFromCube(*conflictCube));  // LCOV_EXCL_LINE
        continue;  // LCOV_EXCL_LINE
      }
      if (!cubeIntersectsInit(problem, solverType, initFormula, obligation.cube)) {
        const StateCube generalizedCube = generalizeInitExcludedCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            initFormula,  // LCOV_EXCL_LINE
            obligation.cube);  // LCOV_EXCL_LINE
        addClauseToFrame(frames[0], clauseFromCube(generalizedCube));  // LCOV_EXCL_LINE
        continue;
      }  // LCOV_EXCL_LINE
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: counterexample candidate reached init ",
            "bad_frame=", obligation.badFrame,
            // LCOV_EXCL_START
            " cube=", obligation.cube.size(),
            " root_cube=", obligation.rootCube.size());
      }
      // LCOV_EXCL_STOP
      if (!refineProjectedCounterexamples) {
        // LCOV_EXCL_START
        // SEC strategy runs a concrete base-case validation immediately after
        // every PDR difference. Projected retry stages therefore do not need to
        // LCOV_EXCL_STOP
        // spend another exact bounded-prefix query here; returning the
        // LCOV_EXCL_START
        // candidate lets the caller either accept a real witness or move to the
        // next precision stage.
        badFrame = obligation.badFrame;
        return false;
      }
      if (problem.observedOutputExprs0.size() > 1 &&
      // LCOV_EXCL_STOP
          !usePerOutputValidatedBadFormulaRepair &&  // LCOV_EXCL_LINE
          !useWholeBatchValidatedBadFormulaRepair &&  // LCOV_EXCL_LINE
          obligation.badFrame >  // LCOV_EXCL_LINE
              kMaxMultiOutputProjectedRootValidationFrame) {
        if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: deferred deep multi-output root validation ",
              "bad_frame=", obligation.badFrame,  // LCOV_EXCL_LINE
              // LCOV_EXCL_START
              " outputs=", problem.observedOutputExprs0.size(),  // LCOV_EXCL_LINE
              " root_cube=", obligation.rootCube.size());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        badFrame = obligation.badFrame;  // LCOV_EXCL_LINE
        return false;  // LCOV_EXCL_LINE
      }
      const bool allowEagerBadFormulaValidationForReject =
          problem.resetBootstrapCycles == 0 ||
          obligation.badFrame == 1 ||
          expandedBadFormulaObligations ||
          useWholeBatchValidatedBadFormulaRepair ||
          usePerOutputValidatedBadFormulaRepair;
      if (learnValidatedBadFormulaClausesOnReject &&
          useEagerBadFormulaValidation &&  // LCOV_EXCL_LINE
          // LCOV_EXCL_STOP
          allowEagerBadFormulaValidationForReject) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        const auto refinement = learnValidatedBadFormulaClauses(  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
              problem,  // LCOV_EXCL_LINE
              solverType,  // LCOV_EXCL_LINE
              transitionByState,  // LCOV_EXCL_LINE
              frameInvariant,  // LCOV_EXCL_LINE
              frames,  // LCOV_EXCL_LINE
              obligation.badFrame,  // LCOV_EXCL_LINE
              badFrame,  // LCOV_EXCL_LINE
              resetFrontierCache,  // LCOV_EXCL_LINE
              useWholeBatchValidatedBadFormulaRepair);  // LCOV_EXCL_LINE
        if (refinement.has_value()) {  // LCOV_EXCL_LINE
          return *refinement;  // LCOV_EXCL_LINE
        }
      }  // LCOV_EXCL_LINE
      const StateCube& concreteTarget =
          obligation.rootCube.empty() ? obligation.cube : obligation.rootCube;
      if (useObservationFrontier) {
        // The startup frontier for this binary SEC slice is the checked top-level
        // observation, not a fully concrete internal reset image.  Use the same
        // base-case frontier query as KI/IMC to validate abstract PDR roots; this
        // avoids treating arbitrary resetless FIFO/memory cells as evidence.
        const bool badPredicateReachable =
            !SEC::provesNoBaseCounterexampleAtFrontier(
                problem, solverType, obligation.badFrame);
        if (!badPredicateReachable) {
          addClauseToFrames(
              frames, clauseFromCube(concreteTarget), obligation.badFrame);
          if (pdrStatsEnabled()) {
            emitSecDiag(
                "SEC PDR stats: refined observation-frontier root ",
                "bad_frame=", obligation.badFrame,
                " root_cube=", concreteTarget.size());
          }
          consumeProjectedCounterexampleRefinementBudget(
              projectedCounterexampleRefinementBudget);
          return true;
        }
        badFrame = obligation.badFrame;
        return false;
      }
      const bool largeDualRailResetFrontier =
          problem.usesDualRailStateEncoding &&
          pdrDualRailStateSymbolCount(problem) >
              dualRailResetFrontierStateSymbolLimit();
      const bool localDualRailLeafRootRepair =
          canRepairLocalDualRailFinalLeafRoot(problem, concreteTarget);
      if (largeDualRailResetFrontier &&
          !localDualRailLeafRootRepair &&
          !useExactResetFrontierChecks &&
          projectedCounterexampleRefinementBudget != nullptr &&
          concreteTarget.size() >=
              kMinLargeDualRailRootForConcreteValidationSkip) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: skipped large dual-rail concrete root ",
              "validation root_cube=", concreteTarget.size(),
              " rail_state_symbols=", pdrDualRailStateSymbolCount(problem));
        }
        markPdrBudgetExhausted(
            PdrBudgetExhaustion::ProjectedCounterexampleRefinement);
        return true;
      }
      const bool preferShallowPerFrameValidation =
          !largeDualRailResetFrontier &&
          obligation.badFrame <= kMaxPerFrameConcreteValidationDepth &&
          concreteTarget.size() <= kMaxPerFrameConcreteValidationCubeLiterals;
      const bool preferCachedConcreteValidation =
          !preferShallowPerFrameValidation &&
          concreteTarget.size() >= kCachedConcreteValidationMinCubeLiterals &&
          (obligation.badFrame >= kCachedConcreteValidationMinDepth ||
           largeDualRailResetFrontier);
      const ConcreteCubeReachabilityMode concreteValidationMode =
          preferCachedConcreteValidation
              ? ConcreteCubeReachabilityMode::CachedAssumptions
              : ConcreteCubeReachabilityMode::OneShotUnitClauses;
      const bool concreteTargetReachable =
          cubeReachableWithinConcreteFrames(
              problem,
              solverType,
              transitionByState,
              concreteTarget,
              obligation.badFrame,
              resetFrontierCache,
              concreteValidationMode,
              frameInvariant);
      if (hasPdrBudgetExhaustion()) {
        return true;  // LCOV_EXCL_LINE
      }
      if (!concreteTargetReachable) {
        // Projected predecessor cubes can be reachable even when the original
        // bad/frontier cube they came from is not.  Before accepting such a
        // path as a counterexample, validate the root cube with the exact
        // bounded transition prefix. If no concrete prefix reaches it, learn a
        // bounded-safe frame clause and keep the ordinary PDR loop going.
        size_t generalizationAttempts = 0;
        // LCOV_EXCL_START
        const StateCube generalizedTarget =
            generalizeBoundedUnreachableRootCube(
            // LCOV_EXCL_STOP
                problem,
                solverType,
                transitionByState,
                concreteTarget,
                obligation.badFrame,
                resetFrontierCache,
                frameInvariant,
                maxBoundedRootGeneralizationAttempts,
                generalizationAttempts);
        const StateClause refinedClause = clauseFromCube(generalizedTarget);
        if (obligation.badFrame == 0) {
          addClauseToFrame(frames[0], refinedClause);  // LCOV_EXCL_LINE
        } else {  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          addClauseToFrames(frames, refinedClause, obligation.badFrame);
          // LCOV_EXCL_STOP
        }
        // Concrete root validation records exact reset-predecessor cores. Drain
        // any singleton F1 cores now, otherwise sibling projected roots can
        // rediscover the same unreachable bus bit one model at a time.
        learnExactResetPredecessorSingletonClauses(
            frames, resetFrontierCache, concreteTarget, obligation.badFrame);
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample ",
              // LCOV_EXCL_START
              "bad_frame=", obligation.badFrame,
              " root_cube=", concreteTarget.size(),
              "->", generalizedTarget.size(),
              " checks=", generalizationAttempts);
        }
        consumeProjectedCounterexampleRefinementBudget(
            projectedCounterexampleRefinementBudget);
        if (learnValidatedBadFormulaClausesOnReject &&
            useSingleOutputValidatedBadFormulaRepair) {  // LCOV_EXCL_LINE
          // The concrete root check records reset-unreachable cores for every
          // LCOV_EXCL_STOP
          // frame it proves. Immediately give the state-only bad-formula
          // repair a chance to consume those cached exact cores, otherwise PDR
          // can rediscover neighboring bad assignments one at a time.
          (void)learnValidatedBadFormulaClauses(  // LCOV_EXCL_LINE
              problem,  // LCOV_EXCL_LINE
              solverType,  // LCOV_EXCL_LINE
              transitionByState,  // LCOV_EXCL_LINE
              frameInvariant,  // LCOV_EXCL_LINE
              frames,  // LCOV_EXCL_LINE
              obligation.badFrame,  // LCOV_EXCL_LINE
              badFrame,  // LCOV_EXCL_LINE
              resetFrontierCache);  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        return true;
      }
      badFrame = obligation.badFrame;
      return false;
    }

    const size_t obligationProjectionLimit =
        predecessorProjectionLimitForObligation(
            obligation.level, predecessorProjectionLimit);

    if (obligation.cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      // For a large target cube, first block a cheap subset.  If no
      // predecessor can reach the subset, then no predecessor can reach the
      // stronger original cube either, and we avoid building a SAT query for a
      // thousand next-state functions just to learn the same small clause.
      const StateCube cheapTarget = boundedCheapTransitionCube(
          obligation.cube, kLargeBlockedCubeSeedSize, problem, transitionByState);
      if (cheapTarget.size() < obligation.cube.size()) {
        const auto cheapPredecessor = findPredecessorCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            // LCOV_EXCL_START
            frames,
            obligation.level - 1,
            cheapTarget,
            false,
            complementPartners,
            obligationProjectionLimit,
            obligationExactFrameClauses,
            &resetFrontierCache,
            &predecessorAssumptionCache,
            // LCOV_EXCL_STOP
            nullptr,
            // LCOV_EXCL_START
            predecessorQueryBudget,
            usePredecessorResetFrontierChecks,
            supportCache);
        if (hasPdrBudgetExhaustion()) {
          return true;  // LCOV_EXCL_LINE
        }
        if (!cheapPredecessor.has_value()) {
        const StateCube generalizedCube = generalizeBlockedCube(  // LCOV_EXCL_LINE
            problem,  // LCOV_EXCL_LINE
            solverType,  // LCOV_EXCL_LINE
            transitionByState,  // LCOV_EXCL_LINE
            initFormula,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            frameInvariant,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            frames,  // LCOV_EXCL_LINE
            obligation.level,  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
            cheapTarget,
            &resetFrontierCache,  // LCOV_EXCL_LINE
            &predecessorAssumptionCache,  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            complementPartners,  // LCOV_EXCL_LINE
            obligationProjectionLimit,  // LCOV_EXCL_LINE
            obligationExactFrameClauses,  // LCOV_EXCL_LINE
            usePredecessorResetFrontierChecks,  // LCOV_EXCL_LINE
            predecessorQueryBudget,  // LCOV_EXCL_LINE
            supportCache);  // LCOV_EXCL_LINE
            // LCOV_EXCL_STOP
        addClauseToFrames(frames, clauseFromCube(generalizedCube), obligation.level);  // LCOV_EXCL_LINE
        learnExactResetPredecessorSingletonClauses(  // LCOV_EXCL_LINE
            frames,  // LCOV_EXCL_LINE
            resetFrontierCache,  // LCOV_EXCL_LINE
            cheapTarget,  // LCOV_EXCL_LINE
            obligation.level);  // LCOV_EXCL_LINE
        // LCOV_EXCL_START
        if (obligation.level < obligation.badFrame) {  // LCOV_EXCL_LINE
        // LCOV_EXCL_STOP
          const StateCube propagatedRoot =
              obligation.rootCube.empty() ? generalizedCube : obligation.rootCube;  // LCOV_EXCL_LINE
          enqueueProofObligation(  // LCOV_EXCL_LINE
              queue,
              queuedKeys,
              ProofObligation{  // LCOV_EXCL_LINE
                  generalizedCube,  // LCOV_EXCL_LINE
                  obligation.level + 1,  // LCOV_EXCL_LINE
                  obligation.badFrame,  // LCOV_EXCL_LINE
                  propagatedRoot});  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        continue;
        } // LCOV_EXCL_LINE
      }  // LCOV_EXCL_LINE
    }

    std::vector<StateClause> projectedFrameRefinements;
    std::unordered_set<StateClause, StateClauseHash> projectedFrameRefinementKeys;
    while (true) {
      const auto predecessor = findPredecessorCube(
          problem,
          solverType,
          transitionByState,
          initFormula,
          frameInvariant,
          frames,
          obligation.level - 1,
          obligation.cube,
          false,
          complementPartners,
          obligationProjectionLimit,
          obligationExactFrameClauses,
          &resetFrontierCache,
          &predecessorAssumptionCache,
          projectedFrameRefinements.empty() ? nullptr : &projectedFrameRefinements,
          predecessorQueryBudget,
          usePredecessorResetFrontierChecks,
          supportCache);
      if (hasPdrBudgetExhaustion()) {
        return true;  // LCOV_EXCL_LINE
      }
      if (!predecessor.has_value()) {
        // No predecessor survives F[level-1], so the cube can be blocked at
        // every frame up to "level". If we needed local projected-frame
        // refinements, learn this exact cube directly rather than re-entering
        // generalization without the same refinement clauses.
        if (projectedFrameRefinements.empty()) {
          learnBlockedObligation(obligation, obligationExactFrameClauses);
        } else {
          learnBlockedObligationVerbatim(obligation);
        }
        break;
      }
      const StateCube queuedPredecessor =
          obligation.level == 1
              ? *predecessor
              : boundedPrefixCube(*predecessor, obligationProjectionLimit);
      ProofObligation predecessorObligation{
          queuedPredecessor,
          obligation.level - 1,
          obligation.badFrame,
          obligation.rootCube};
      const StateClause predecessorClause =
          clauseFromCube(predecessorObligation.cube);
      const auto blockingClause =
          !obligationExactFrameClauses
              ? findSubsumingFrameClause(
                    // LCOV_EXCL_START
                    frames[predecessorObligation.level], predecessorClause)
                    // LCOV_EXCL_STOP
              : std::optional<StateClause>{};
      if (blockingClause.has_value()) {
        // Projected frame encoding is sound but incomplete: it may omit the
        // learned clause that already blocks this predecessor.  Re-enqueueing
        // such a stale predecessor creates a reset-frontier loop. Refine only
        // this local SAT query with the missing learned blocker instead of
        // rebuilding the query with every clause from the full frame.
        if (projectedFrameRefinementKeys.insert(*blockingClause).second) {
          projectedFrameRefinements.push_back(*blockingClause);
          if (pdrStatsEnabled()) {
            const size_t retryNumber = nextPdrProjectedBlockedRetryNumber();
            if (retryNumber <= kInitialPdrStatsQueries ||
                retryNumber % pdrStatsInterval() == 0) {  // LCOV_EXCL_LINE
              emitSecDiag(
                  "SEC PDR stats: projected-frame refinement #", retryNumber,
                  " level=", obligation.level,
                  " cube=", obligation.cube.size(),
                  " predecessor=", predecessorObligation.cube.size(),
                  " refinements=", projectedFrameRefinements.size());
            }
          }
          if (projectedFrameRefinements.size() <
              maxProjectedFrameRefinementsBeforeExactRetry()) {
            continue;
          }
          // LCOV_EXCL_START
          if (pdrStatsEnabled()) {
          // LCOV_EXCL_STOP
            emitSecDiag(
                // LCOV_EXCL_START
                "SEC PDR stats: projected-frame refinement cap reached ",
                "level=", obligation.level,
                " cube=", obligation.cube.size(),
                " predecessor=", predecessorObligation.cube.size(),
                // LCOV_EXCL_STOP
                " refinements=", projectedFrameRefinements.size());
          }
        } else if (pdrStatsEnabled()) {
          // If the same blocker was already added and the projected query still
          // returns a predecessor blocked by it, keep the algorithm
          // conservative: fall back to the exact-frame path once instead of
          // spinning forever.
          emitSecDiag(  // LCOV_EXCL_LINE
              "SEC PDR stats: exact retry for duplicate projected blocker ",
              "level=", obligation.level,  // LCOV_EXCL_LINE
              " cube=", obligation.cube.size(),  // LCOV_EXCL_LINE
              " predecessor=", predecessorObligation.cube.size());  // LCOV_EXCL_LINE
        }  // LCOV_EXCL_LINE
        const auto exactPredecessor = findPredecessorCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            obligation.level - 1,
            obligation.cube,
            false,
            // LCOV_EXCL_START
            complementPartners,
            obligationProjectionLimit,
            true,
            &resetFrontierCache,
            &predecessorAssumptionCache,
            nullptr,
            predecessorQueryBudget,
            usePredecessorResetFrontierChecks,
            supportCache);
            // LCOV_EXCL_STOP
        if (hasPdrBudgetExhaustion()) {
          return true;  // LCOV_EXCL_LINE
        }
        if (!exactPredecessor.has_value()) {
          learnBlockedObligation(obligation, true);
          break;
        }
        const StateCube exactQueuedPredecessor =
            obligation.level == 1  // LCOV_EXCL_LINE
                ? *exactPredecessor  // LCOV_EXCL_LINE
                : boundedPrefixCube(*exactPredecessor, obligationProjectionLimit);  // LCOV_EXCL_LINE
        predecessorObligation = ProofObligation{  // LCOV_EXCL_LINE
            exactQueuedPredecessor,  // LCOV_EXCL_LINE
            obligation.level - 1,  // LCOV_EXCL_LINE
            obligation.badFrame,  // LCOV_EXCL_LINE
            obligation.rootCube};  // LCOV_EXCL_LINE
      }
      enqueueProofObligation(queue, queuedKeys, obligation);
      enqueueProofObligation(queue, queuedKeys, predecessorObligation);
      break;
    }
  }

  return true;
}

std::vector<StateClause> buildSeedClauses(const KInductionProblem& problem,
                                          const InitFactIndex& initFacts) {
  std::vector<StateClause> seedClauses;
  if (!KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
    return seedClauses;
  }
  // Seed the first learned frame with state equalities that are already
  // guaranteed by Init/bootstrap, so PDR starts from facts that are known
  // reachable-state invariants instead of rediscovering them from scratch.
  //
  // This deliberately uses only structured init/bootstrap facts. Running an
  // exact SAT init-intersection query for every possible equality seed is too
  // expensive on ASIC regressions and is not needed for soundness: if a seed is
  // not cheaply known to hold on the startup frontier, we simply do not seed it.
  for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
    StateClause clause0 = {{lhsSymbol, false}, {rhsSymbol, true}};
    StateClause clause1 = {{lhsSymbol, true}, {rhsSymbol, false}};
    normalizeClause(clause0);
    normalizeClause(clause1);

    // Promote already-anchored state equalities into initial frame facts when
    // they are guaranteed by Init/bootstrap instead of guessed from structure.
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, true, rhsSymbol, false)) {
      seedClauses.push_back(clause0);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, false, rhsSymbol, true)) {
      seedClauses.push_back(clause1);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }
  return seedClauses;
}

BoolExpr* buildStateEqualityInvariant(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  if (equalityPairs.empty()) {
    return nullptr;
  }

  BoolExpr* invariant = BoolExpr::createTrue();
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    invariant = BoolExpr::And(
        invariant,
        makeEqualityExpr(BoolExpr::Var(lhsSymbol), BoolExpr::Var(rhsSymbol)));
  }
  invariant = BoolExpr::simplify(invariant);
  return invariant == BoolExpr::createTrue() ? nullptr : invariant;
}

BoolExpr* buildStateEqualityInvariant(const KInductionProblem& problem) {
  return buildStateEqualityInvariant(problem.inductiveStateEqualityPairs);
}

bool structuredInitFactsProveEqualityPair(const InitFactIndex& initFacts,
                                          const std::pair<size_t, size_t>& pair) {
  // A structured Init/bootstrap equality proves `lhs == rhs` exactly when both
  // violating two-literal cubes are excluded from the startup frontier.
  return twoLiteralCubeIsKnownOutsideInit(
             initFacts, pair.first, true, pair.second, false) &&
         twoLiteralCubeIsKnownOutsideInit(
             initFacts, pair.first, false, pair.second, true);
}

bool structuredInitFactsImplyStateEqualities(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  if (equalityPairs.empty() || !hasStructuredInitFacts(problem)) {
    return false;
  }

  const InitFactIndex initFacts = buildInitFactIndex(problem);
  for (const auto& pair : equalityPairs) {
    if (!structuredInitFactsProveEqualityPair(initFacts, pair)) {
      return false;
    }
  }
  return true;
}

bool structuredInitFactsImplyCandidate(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    bool alsoRequireOutputProperty,
    KEPLER_FORMAL::Config::SolverType solverType) {
  if (!structuredInitFactsImplyStateEqualities(problem, equalityPairs)) {
    return false;
  }
  if (!alsoRequireOutputProperty) {
    return true;
  }
  // State/output candidates combine structured startup equalities with the
  // ordinary top-output property.  The structured shortcut may prove only the
  // LCOV_EXCL_START
  // state half; the output half must still be present in the validated F[0]
  // LCOV_EXCL_STOP
  // formula before PDR can use the combined invariant.
  return problem.property != nullptr &&
         initialFrontierImplies(initFormula, problem.property, solverType);
}

bool pdrInitialFrontierImpliesStateEqualities(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    KEPLER_FORMAL::Config::SolverType solverType) {
  // Structured startup equalities are exact F0 facts; consult them before
  // building a broad monolithic Init SAT query for the same relation.
  if (structuredInitFactsImplyStateEqualities(problem, equalityPairs)) {
    return true;
  }
  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  if (initialFrontierImplies(initFormula, invariant, solverType)) {
    return true;
  }
  return false;
}

// LCOV_EXCL_START
BoolExpr* buildStateAndOutputInvariant(
    const KInductionProblem& problem,
    // LCOV_EXCL_STOP
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  // This strengthening is meant to add top-output equality to real
  // state-correspondence facts.  Without at least one state pair it degenerates
  // into the property itself and bypasses PDR repair paths that still need to
  // be exercised and validated independently.
  if (equalityPairs.empty()) {
    return nullptr;
  }

  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr) {
    invariant = BoolExpr::createTrue();  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  for (size_t output = 0;
       output < problem.observedOutputExprs0.size() &&
       output < problem.observedOutputExprs1.size();
       ++output) {
    invariant = BoolExpr::And(
        invariant,
        makeEqualityExpr(
            problem.observedOutputExprs0[output],
            problem.observedOutputExprs1[output]));
  }
  invariant = BoolExpr::simplify(invariant);
  return invariant == BoolExpr::createTrue() ? nullptr : invariant;
}

std::vector<size_t> stateEqualitySymbols(
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  std::unordered_set<size_t> symbols;
  // LCOV_EXCL_START
  symbols.reserve(equalityPairs.size() * 2);
  // LCOV_EXCL_STOP
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    symbols.insert(lhsSymbol);
    symbols.insert(rhsSymbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

bool pdrStateEqualitySubsetCacheEntryMatches(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    const PdrStateEqualitySubsetCacheEntry& entry) {
  return entry.inputPairs == equalityPairs &&
         entry.resetBootstrapInputs == problem.resetBootstrapInputs &&
         entry.resetBootstrapCycles == problem.resetBootstrapCycles &&
         entry.initialStateAssignments == problem.initialStateAssignments &&
         entry.initialStateEqualityPairs == problem.initialStateEqualityPairs &&
         entry.bootstrapStateAssignments == problem.bootstrapStateAssignments &&
         entry.bootstrapStateEqualityPairs == problem.bootstrapStateEqualityPairs;
}

std::optional<std::vector<std::pair<size_t, size_t>>>
lookupCachedPdrStateEqualitySubset(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  if (problem.lazyTransitions == nullptr) {
    return std::nullopt;
  }
  for (const auto& entry :
       problem.lazyTransitions->pdrStateEqualitySubsetCache) {
    if (pdrStateEqualitySubsetCacheEntryMatches(
            problem, equalityPairs, entry)) {
      return entry.selectedPairs;
    }
  }
  return std::nullopt;
}

void rememberCachedPdrStateEqualitySubset(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& inputPairs,
    const std::vector<std::pair<size_t, size_t>>& selectedPairs) {
  if (problem.lazyTransitions == nullptr || selectedPairs.empty()) {
    return;
  }
  auto& cache = problem.lazyTransitions->pdrStateEqualitySubsetCache;
  for (auto& entry : cache) {
    if (pdrStateEqualitySubsetCacheEntryMatches(problem, inputPairs, entry)) { // LCOV_EXCL_LINE
      entry.selectedPairs = selectedPairs; // LCOV_EXCL_LINE
      return; // LCOV_EXCL_LINE
    }
  }
  PdrStateEqualitySubsetCacheEntry entry;
  entry.inputPairs = inputPairs;
  entry.resetBootstrapInputs = problem.resetBootstrapInputs;
  entry.resetBootstrapCycles = problem.resetBootstrapCycles;
  entry.initialStateAssignments = problem.initialStateAssignments;
  entry.initialStateEqualityPairs = problem.initialStateEqualityPairs;
  entry.bootstrapStateAssignments = problem.bootstrapStateAssignments;
  entry.bootstrapStateEqualityPairs = problem.bootstrapStateEqualityPairs;
  entry.selectedPairs = selectedPairs;
  cache.push_back(std::move(entry));
}

bool equalityPairViolatedAtFrame(const SATSolverWrapper& solver,
                                 const FrameVariableStore& variables,
                                 const std::pair<size_t, size_t>& pair,
                                 size_t frame) {
  if (!variables.hasSymbol(pair.first) || !variables.hasSymbol(pair.second)) {
    return false;  // LCOV_EXCL_LINE
  }
  return solver.getLiteralValue(variables.getLiteral(pair.first, frame)) !=
         solver.getLiteralValue(variables.getLiteral(pair.second, frame));
}

std::optional<std::vector<std::pair<size_t, size_t>>>
pruneStateEqualitySubsetByInductiveCounterexample(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs,
    BoolExpr* invariant,
    KEPLER_FORMAL::Config::SolverType solverType) {
  const std::vector<size_t> invariantSymbols = stateEqualitySymbols(equalityPairs);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, invariantSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);

  std::unordered_set<size_t> querySymbols(
      invariantSymbols.begin(), invariantSymbols.end());
  querySymbols.insert(encodedTargets.begin(), encodedTargets.end());
  querySymbols.insert(
      transitionSupportSymbols.begin(), transitionSupportSymbols.end());
  addRelevantComplementedStatePartners(problem.complementedStatePairs0, querySymbols);
  addRelevantComplementedStatePartners(problem.complementedStatePairs1, querySymbols);
  addRelevantSameFrameStateEqualityPartners(problem, querySymbols);
  addRelevantDualRailPartners(problem.dualRailStatePairs, querySymbols);

  const auto solverSymbols = sortUniqueSymbols(std::move(querySymbols));
  const auto querySolverType = stateEqualitySubsetSolverType(
      problem, solverType, equalityPairs.size(), solverSymbols.size());
  if (pdrStatsEnabled() && querySolverType != solverType) {
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: state equality subset solver=cadical symbols=",
        solverSymbols.size(), // LCOV_EXCL_LINE
        " pairs=",
        equalityPairs.size()); // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
  SATSolverWrapper solver(querySolverType);
  // This local SAT query is part of PDR's invariant-pruning path, not a
  // standalone preprocessing proof. Keep the selected backend on the same
  // short-lived PDR query profile as predecessor and bad-state checks.
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
  addSameFrameStateEqualities(solver, variables, problem, 2);
  addDualRailStateValidity(solver, variables, problem.dualRailStatePairs, 2);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  addTransitionRelationForTargets(
      solver,
      variables,
      transitionByState,
      0,
      encodedTargets,
      transitionSupportSymbols);

  FrameFormulaEncoder currentEncoder(
      solver, variables.makeLeafLits(0, invariantSymbols));
  FrameFormulaEncoder nextEncoder(
      solver, variables.makeLeafLits(1, invariantSymbols));
  solver.addClause({currentEncoder.encode(invariant)});
  // LCOV_EXCL_START
  solver.addClause({nextEncoder.encode(BoolExpr::Not(invariant))});
  // LCOV_EXCL_STOP
  if (!solver.solve()) {
    return std::nullopt;
  }

  std::vector<std::pair<size_t, size_t>> keptPairs;
  keptPairs.reserve(equalityPairs.size());
  for (const auto& pair : equalityPairs) {
    if (!equalityPairViolatedAtFrame(solver, variables, pair, 1)) {
      keptPairs.push_back(pair);
    }
  }
  if (keptPairs.size() == equalityPairs.size()) {
    return std::vector<std::pair<size_t, size_t>>{};  // LCOV_EXCL_LINE
  }
  return keptPairs;
}

BoolExpr* selectInductiveStateEqualitySubsetInvariant(
    const KInductionProblem& problem,
    BoolExpr* initFormula,
    KEPLER_FORMAL::Config::SolverType solverType,
    std::vector<std::pair<size_t, size_t>>* selectedPairs = nullptr) {
  if (problem.inductiveStateEqualityPairs.empty() ||
      problem.inductiveStateEqualityPairs.size() > kMaxStateEqualitySubsetPairs) {
    return nullptr;
  }

  std::vector<std::pair<size_t, size_t>> equalityPairs =
      problem.inductiveStateEqualityPairs;
  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr ||
      !pdrInitialFrontierImpliesStateEqualities(
          problem, initFormula, equalityPairs, solverType)) {
    return nullptr;  // LCOV_EXCL_LINE
  }
  if (const auto cachedSubset =
          lookupCachedPdrStateEqualitySubset(problem, equalityPairs);
      cachedSubset.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag( // LCOV_EXCL_LINE
          "SEC PDR stats: frame invariant state_equality_subset cache hit ",
          "pairs=", cachedSubset->size()); // LCOV_EXCL_LINE
    } // LCOV_EXCL_LINE
    invariant = buildStateEqualityInvariant(*cachedSubset);
    if (selectedPairs != nullptr) {
      *selectedPairs = *cachedSubset;
    }
    return invariant;
  }

  TransitionExprResolver transitionByState(problem);
  for (size_t iteration = 0;
       iteration < kMaxStateEqualitySubsetIterations && !equalityPairs.empty();
       ++iteration) {
    invariant = buildStateEqualityInvariant(equalityPairs);
    auto prunedPairs = pruneStateEqualitySubsetByInductiveCounterexample(
        problem, transitionByState, equalityPairs, invariant, solverType);
    if (!prunedPairs.has_value()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: frame invariant state_equality_subset support=",
            invariant->getSupportVars().size(),
            " pairs=", equalityPairs.size(),
            " iterations=", iteration + 1,
            " init=pass inductive=pass");
      // LCOV_EXCL_START
      }
      // LCOV_EXCL_STOP
      if (selectedPairs != nullptr) {
        // LCOV_EXCL_START
        *selectedPairs = equalityPairs;
        // LCOV_EXCL_STOP
      }
      rememberCachedPdrStateEqualitySubset(
          problem, problem.inductiveStateEqualityPairs, equalityPairs);
      // LCOV_EXCL_START
      return invariant;
      // LCOV_EXCL_STOP
    }
    if (prunedPairs->empty()) {
      break; // LCOV_EXCL_LINE
    }
    equalityPairs = std::move(*prunedPairs);
  }

  if (pdrStatsEnabled()) { // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: frame invariant state_equality_subset unavailable ",
        "remaining_pairs=", equalityPairs.size(),  // LCOV_EXCL_LINE
        " iterations=", kMaxStateEqualitySubsetIterations);
  }  // LCOV_EXCL_LINE
  return nullptr; // LCOV_EXCL_LINE
}

BoolExpr* selectPdrFrameInvariant(const KInductionProblem& problem,
                                  // LCOV_EXCL_START
                                  BoolExpr* initFormula,
                                  // LCOV_EXCL_STOP
                                  KEPLER_FORMAL::Config::SolverType solverType) {
  if (!KEPLER_FORMAL::Config::getSecInternalStateCorrespondence()) {
    return nullptr;
  }
  // PDR can use already inferred SEC facts as a strengthening invariant, but
  // only after validating the same two proof obligations that make any frame
  // invariant sound:
  //   1. the startup/reset frontier implies it, and
  //   2. one transition step preserves it.
  //
  // This is not a separate "fast proof" path. The invariant is fed back into
  // the ordinary bad-cube and predecessor queries below, so PDR still performs
  // the frame/blocking/convergence algorithm. It simply avoids relearning the
  // same state-equality facts one clause at a time on large SEC designs.
  if (initFormula == nullptr) {
    return nullptr;  // LCOV_EXCL_LINE
  }

  FormulaSupportCache invariantSupportCache;
  auto validateCandidate =
      [&](const char* label,
          BoolExpr* candidate,
          const std::vector<std::pair<size_t, size_t>>* stateEqualityPairs =
              nullptr,
          bool alsoRequireOutputProperty = false) -> BoolExpr* {
    if (candidate == nullptr) {
      if (pdrStatsEnabled()) {
        emitSecDiag("SEC PDR stats: frame invariant ", label, " unavailable");
      }
      return nullptr;
    }

    bool initImpliesCandidate =
        initialFrontierImplies(initFormula, candidate, solverType);
    if (!initImpliesCandidate && stateEqualityPairs != nullptr) {
      initImpliesCandidate = structuredInitFactsImplyCandidate(
          problem,
          initFormula,
          *stateEqualityPairs,
          alsoRequireOutputProperty,
          solverType);
    }
    const bool inductive =
        initImpliesCandidate &&
        isInductiveInvariant(
            problem, candidate, solverType, invariantSupportCache);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: frame invariant ", label,
          " support=", candidate->getSupportVars().size(),
          " init=", initImpliesCandidate ? "pass" : "fail",
          " inductive=", inductive ? "pass" : "fail");
    }
    if (!initImpliesCandidate || !inductive) {
      return nullptr;
    }
    return candidate;
  };

  auto selectSharedStrengthening = [&]() -> BoolExpr* {
    // The shared SEC strengthening can be stronger than a pruned equality
    // LCOV_EXCL_START
    // subset.  It still has to pass the same init and one-step inductiveness
    // LCOV_EXCL_STOP
    // checks before PDR may use it as a frame fact.
    // LCOV_EXCL_START
    BoolExpr* sharedStrengthening =
    // LCOV_EXCL_STOP
        selectValidatedStrengtheningInvariant(problem, initFormula, solverType);
    // LCOV_EXCL_START
    return validateCandidate("shared_strengthening", sharedStrengthening);
    // LCOV_EXCL_STOP
  };

  if (BoolExpr* stateInvariant =
          validateCandidate(
              "state_equalities",
              buildStateEqualityInvariant(problem),
              &problem.inductiveStateEqualityPairs)) {
    if (isSecDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: PDR using validated state-equality frame invariant with ",
          problem.inductiveStateEqualityPairs.size(),  // LCOV_EXCL_LINE
          // LCOV_EXCL_START
          " equality pairs");
          // LCOV_EXCL_STOP
    }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    return stateInvariant;  // LCOV_EXCL_LINE
    // LCOV_EXCL_STOP
  }

  if (BoolExpr* stateOutputInvariant =
          validateCandidate(
              "state_equalities_outputs",
              buildStateAndOutputInvariant(
                  problem, problem.inductiveStateEqualityPairs),
              &problem.inductiveStateEqualityPairs,
              /*alsoRequireOutputProperty=*/true)) {
    if (isSecDiagEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: PDR using validated state/output frame invariant");
    }  // LCOV_EXCL_LINE
    return stateOutputInvariant;
  }

  std::vector<std::pair<size_t, size_t>> stateSubsetPairs;
  if (BoolExpr* stateSubsetInvariant =
          selectInductiveStateEqualitySubsetInvariant(
              problem, initFormula, solverType, &stateSubsetPairs)) {
    // LCOV_EXCL_START
    // A state-only subset may be inductive but too weak to exclude the output
    // LCOV_EXCL_STOP
    // mismatch, causing PDR to rediscover the output equality as thousands of
    // LCOV_EXCL_START
    // tiny blocking clauses.  Strengthen that subset with the current output
    // LCOV_EXCL_STOP
    // equality only when the combined formula is itself proved valid on Init
    // and inductive across one transition.  The result is still just a PDR
    // frame fact; it is not an external fast proof path.
    if (BoolExpr* outputStrengthenedInvariant =
            validateCandidate(
                // LCOV_EXCL_START
                "state_equality_subset_outputs",
                // LCOV_EXCL_STOP
                buildStateAndOutputInvariant(problem, stateSubsetPairs),
                // LCOV_EXCL_START
                &stateSubsetPairs,
                // LCOV_EXCL_STOP
                /*alsoRequireOutputProperty=*/true)) {
      if (isSecDiagEnabled()) {  // LCOV_EXCL_LINE
        emitSecDiag(  // LCOV_EXCL_LINE
            // LCOV_EXCL_START
            "SEC diag: PDR using validated state/output subset frame invariant");
      }  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
      return outputStrengthenedInvariant;  // LCOV_EXCL_LINE
    // LCOV_EXCL_START
    }


// LCOV_EXCL_STOP
    if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
      if (isSecDiagEnabled()) {
        emitSecDiag(  // LCOV_EXCL_LINE
            "SEC diag: PDR using validated SEC strengthening frame invariant");
      }  // LCOV_EXCL_LINE
      return strengthenedInvariant;
    }

// LCOV_EXCL_START


// LCOV_EXCL_STOP
    if (isSecDiagEnabled()) {  // LCOV_EXCL_LINE
      // LCOV_EXCL_START
      emitSecDiag(  // LCOV_EXCL_LINE
      // LCOV_EXCL_STOP
          "SEC diag: PDR using validated state-equality subset frame invariant");
    }  // LCOV_EXCL_LINE
    return stateSubsetInvariant;  // LCOV_EXCL_LINE
  }

  // Some SEC proofs need the full extracted strengthening lemma, not just the
  // raw state-equality core. This is still used as a PDR frame constraint only
  // after the same inductiveness check succeeds.
  if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
    if (isSecDiagEnabled()) { // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC diag: PDR using validated SEC strengthening frame invariant");
    }  // LCOV_EXCL_LINE
    return strengthenedInvariant; // LCOV_EXCL_LINE
  }
  return nullptr;
}

void propagateClauses(const KInductionProblem& problem,
                      KEPLER_FORMAL::Config::SolverType solverType,
                      const TransitionExprResolver& transitionByState,
                      BoolExpr* initFormula,
                      BoolExpr* frameInvariant,
                      std::vector<FrameClauses>& frames,
                      size_t maxLevel,
                      const ComplementPartnerIndex& complementPartners,
                      size_t predecessorProjectionLimit,
                      bool exactFrameClauses,
                      PredecessorAssumptionCache* predecessorAssumptionCache,
                      size_t* predecessorQueryBudget,
                      PdrFormulaSupportCache* supportCache) {
  // Standard PDR propagation: if F[i] /\ T implies a clause on the next frame,
  // move that clause forward into F[i+1].
  for (size_t level = 1; level <= maxLevel; ++level) {
    const auto snapshot = frames[level].clauses;
    for (const auto& clause : snapshot) {
      // Only propagate clauses that are not already known to hold on the next frame,
      // otherwise we would be doing redundant work and risking over-blocking by
      // adding the same clause again after generalization.
      if (frameHasSubsumingClause(frames[level + 1], clause)) {
        continue;
      }
      const StateCube violatingCube = cubeFromClauseNegation(clause);
      // A clause is only safe to propagate if it does not block a real bad path, so check
      // whether any predecessor of the negated cube survives in the current frame. If not, the
      // clause can be added to the next frame without risking over-blocking.
      const auto predecessor = findPredecessorCube(
          problem,
          solverType,
          transitionByState,
          initFormula,
          frameInvariant,
          frames,
          level,
          violatingCube,
          false,
          complementPartners,
          predecessorProjectionLimit,
          exactFrameClauses,
          nullptr,
          predecessorAssumptionCache,
          nullptr,
          predecessorQueryBudget,
          true,
          supportCache);
      if (hasPdrBudgetExhaustion()) {
        return;  // LCOV_EXCL_LINE
      }
      if (!predecessor.has_value()) {
        addClauseToFrame(frames[level + 1], clause);
      }
    // LCOV_EXCL_START
    }
    // LCOV_EXCL_STOP
  }
}

bool isSecPdrTraceEnabled() {
  return std::getenv("KEPLER_SEC_PDR_TRACE") != nullptr;
}

std::string formatSymbolForPdrTrace(size_t symbol) {
  if (symbol == 0) {
    return "FALSE";  // LCOV_EXCL_LINE
  }
  if (symbol == 1) {
    return "TRUE";  // LCOV_EXCL_LINE
  }
  return "x" + std::to_string(symbol);
}

std::string formatCubeForPdrTrace(const StateCube& cube) {
  std::ostringstream oss;
  oss << "{";
  for (size_t i = 0; i < cube.size(); ++i) {
    if (i != 0) {
      // LCOV_EXCL_START
      oss << ", ";
    }
    // LCOV_EXCL_STOP
    oss << formatSymbolForPdrTrace(cube[i].symbol) << "=" << (cube[i].value ? "1" : "0");
  }
  oss << "}";
  return oss.str();
}

std::string formatClauseForPdrTrace(const StateClause& clause) {
  std::ostringstream oss;
  oss << "(";
  for (size_t i = 0; i < clause.size(); ++i) {
    if (i != 0) {
      oss << " OR ";  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
    if (!clause[i].positive) {
      oss << "!";
    }
    oss << formatSymbolForPdrTrace(clause[i].symbol);
  }
  oss << ")";
  return oss.str();
}

std::string formatFramesForPdrTrace(const std::vector<FrameClauses>& frames) {
  std::ostringstream oss;
  for (size_t level = 0; level < frames.size(); ++level) {
    oss << "  F[" << level << "]: ";
    if (level == 0) {
      oss << "Init";
    }
    oss << "\n";
    if (frames[level].clauses.empty()) {
      oss << "    <empty>\n";
      continue;
    }
    for (const auto& clause : frames[level].clauses) {
      oss << "    " << formatClauseForPdrTrace(clause) << "\n";
    }
  }
  return oss.str();
}

void emitPdrTrace(std::string_view label, const std::string& body) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  emitSecDiag("SEC PDR trace: ", label, "\n", body);
}

void emitPdrTraceProblem(const KInductionProblem& problem) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  // Full formula formatting recursively walks every transition/property DAG.
  // That is useful for small debug tests, but on ASIC-size SEC problems it can
  // allocate gigabytes before PDR starts.  Keep the expensive string build
  // strictly behind the explicit PDR trace flag.
  emitSecDiag("SEC PDR trace: problem\n", formatKInductionProblemForDebug(problem));
}

void emitPdrTraceFrames(std::string_view label,
                        const std::vector<FrameClauses>& frames) {
  if (!isSecPdrTraceEnabled()) {
    return;
  }
  emitSecDiag("SEC PDR trace: ", label, "\n", formatFramesForPdrTrace(frames));
}

std::optional<PDRResult> checkResetBootstrapFrameZero(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    bool& resetBootstrapFrameCheckedSafe) {
  if (problem.resetBootstrapCycles == 0 || resetBootstrapFrameCheckedSafe) {
    return std::nullopt;
  }
  const size_t transitionSources = pdrTransitionSourceCount(problem);
  const size_t transitionSourceLimit =
      dualRailResetBootstrapBmcTransitionSourceLimit();
  const size_t observedOutputCount = problem.observedOutputExprs0.size();
  if (detail::pdrResetBootstrapPrecheckTooLarge(
          problem.usesDualRailStateEncoding,
          observedOutputCount,
          problem.originalObservedOutputCount,
          transitionSources,
          transitionSourceLimit,
          kMaxDualRailResetBootstrapBmcObservedOutputs)) {
    // This precheck is an accelerator that lets PDR add the property as an F0
    // fact after reset.  On large dual-rail cones it can become the whole run;
    // check the original property width as well as the current batch so output
    // slicing cannot re-enable the expensive whole-transition BMC. Skipping is
    // conservative: PDR works from the weaker bootstrap summary instead.
    if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
      emitSecDiag(  // LCOV_EXCL_LINE
          "SEC PDR stats: skipped dual-rail reset-bootstrap BMC precheck ",
          // LCOV_EXCL_START
          "transition_sources=", transitionSources,
          " outputs=", observedOutputCount,
          " original_outputs=", problem.originalObservedOutputCount,
          // LCOV_EXCL_STOP
          " transition_limit=", transitionSourceLimit,
          " output_limit=", kMaxDualRailResetBootstrapBmcObservedOutputs);
    }  // LCOV_EXCL_LINE
    return std::nullopt;
  }

  // A reset-bootstrap frontier may be summarized by only the state facts the
  // extractor could prove cheaply. Before PDR treats that summary as F[0], run
  // the concrete one-shot reset BMC used by the other SEC engines. If it finds
  // a real bad post-reset state, report it; otherwise PDR is allowed to add the
  // checked property as a safe F[0] fact below.
  if (auto witness = findBaseCounterexample(problem, solverType, 0);
      witness.has_value()) {
    return PDRResult{PDRStatus::Different, witness->badFrame};  // LCOV_EXCL_LINE
  }
  resetBootstrapFrameCheckedSafe = true;
  return std::nullopt;
}

BoolExpr* buildPdrInitFormula(const KInductionProblem& problem,
                              bool resetBootstrapFrameCheckedSafe) {
  // PDR encodes structured init/bootstrap facts cone-locally in every query.
  // When those facts exist, a monolithic BoolExpr init formula is only a
  // placeholder for invariant/property composition and can be `true`.
  BoolExpr* initFormula = hasStructuredInitFacts(problem)
                              ? BoolExpr::createTrue()
                              : buildProofInitFormula(problem);
  if (initFormula == nullptr && problem.resetBootstrapCycles != 0) {
    // A pruned dual-rail reset slice may have no local bootstrap facts after
    // the broad reset-BMC precheck is skipped.  Running PDR from `true` is a
    // conservative all-state frontier: any convergence proof is stronger than
    // the concrete reset frontier, while abstract bad states are still handled
    // by the normal blocking/validation path.
    initFormula = BoolExpr::createTrue();
  }
  if (problem.resetBootstrapCycles == 0 ||
      !resetBootstrapFrameCheckedSafe ||
      problem.property == nullptr) {
    return initFormula;
  }

  // The bootstrap summary is an abstraction of the reset-unrolled frontier, not
  // necessarily the exact set of post-reset states. Once concrete BMC proved no
  // k=0 SEC mismatch, the SEC property itself is a valid F[0] fact. PDR is run
  // on output batches for wide SEC problems, so this guard stays local to the
  // current property slice instead of materializing the full design property in
  // every SAT query.
  return BoolExpr::simplify(
      BoolExpr::And(
          initFormula != nullptr ? initFormula : BoolExpr::createTrue(),
          problem.property));
}

}  // namespace

PDREngine::PDREngine(const KInductionProblem& problem,
                     KEPLER_FORMAL::Config::SolverType solverType,
                     size_t predecessorProjectionLimit,
                     size_t preciseBadCubeStateLimit,
                     bool useExactFrameClauses,
                     size_t maxPredecessorQueries,
                     bool refineProjectedCounterexamples,
                     size_t maxBoundedRootGeneralizationAttempts,
                     bool learnValidatedBadFormulaClauses,
                     bool useExactResetFrontierChecks,
                     size_t maxProjectedCounterexampleRefinements)
    : problem_(problem),
      solverType_(solverType),
      predecessorProjectionLimit_(predecessorProjectionLimit),
      useExactFrameClauses_(useExactFrameClauses ||
                            predecessorProjectionLimit == 0),
      preciseBadCubeStateLimit_(preciseBadCubeStateLimit),
      maxPredecessorQueries_(maxPredecessorQueries),
      refineProjectedCounterexamples_(refineProjectedCounterexamples),
      maxBoundedRootGeneralizationAttempts_(
          maxBoundedRootGeneralizationAttempts),
      learnValidatedBadFormulaClauses_(learnValidatedBadFormulaClauses),
      useExactResetFrontierChecks_(shouldUseExactResetFrontierChecks(
          problem, useExactResetFrontierChecks)),
      maxProjectedCounterexampleRefinements_(
          maxProjectedCounterexampleRefinements) {
  if (pdrStatsEnabled() && useExactResetFrontierChecks &&
      !useExactResetFrontierChecks_) {
    emitSecDiag(
        "SEC PDR stats: exact reset-frontier checks disabled for large ",
        "dual-rail problem rail_state_symbols=",
        // LCOV_EXCL_START
        pdrDualRailStateSymbolCount(problem),
        // LCOV_EXCL_STOP
        " rail_limit=", dualRailResetFrontierStateSymbolLimit(),
        " transition_sources=", pdrTransitionSourceCount(problem),
        " transition_limit=", dualRailResetFrontierTransitionSourceLimit(),
        " outputs=", problem.observedOutputExprs0.size(),
        " original_outputs=", pdrOriginalObservedOutputCount(problem),
        " output_limit=", kMaxExactResetFrontierDualRailObservedOutputs,
        " original_output_limit=", kMaxExactResetFrontierDualRailOriginalOutputs,
        " medium_state_min=",
        kMinExactResetFrontierDualRailMediumStateSymbols);
  }
}

PDRResult PDREngine::run(size_t maxFrames,
                         bool resetBootstrapFrameCheckedSafe) const {
  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  const bool useLocalFinalLeafRepairBudgets =
      usesLocalDualRailFinalLeafRepairBudgets(
          problem_, useExactFrameClauses_, refineProjectedCounterexamples_);
  const size_t effectiveMaxPredecessorQueries =
      useLocalFinalLeafRepairBudgets
          ? effectiveLocalDualRailFinalLeafBudget(
                maxPredecessorQueries_,
                kMinLocalDualRailFinalLeafPredecessorQueries)
          : maxPredecessorQueries_;
  const size_t effectivePredecessorProjectionLimit =
      useLocalFinalLeafRepairBudgets
          ? effectiveLocalDualRailFinalLeafProjectionLimit(
                predecessorProjectionLimit_)
          : predecessorProjectionLimit_;
  const size_t effectiveMaxProjectedCounterexampleRefinements =
      useLocalFinalLeafRepairBudgets
          ? effectiveLocalDualRailFinalLeafBudget(
                maxProjectedCounterexampleRefinements_,
                kMinLocalDualRailFinalLeafProjectedRefinements)
          : maxProjectedCounterexampleRefinements_;
  resetPdrBudgetExhaustion();
  setPdrPredecessorQueryLimit(effectiveMaxPredecessorQueries);
  setPdrProjectedCounterexampleRefinementLimit(
      effectiveMaxProjectedCounterexampleRefinements);
  emitPdrTraceProblem(problem_);
  if (const auto resetProof = checkResetBootstrapFrameZero(
          problem_, solverType_, resetBootstrapFrameCheckedSafe);
      resetProof.has_value()) {
    return *resetProof;  // LCOV_EXCL_LINE
  }

  BoolExpr* initFormula =
      buildPdrInitFormula(problem_, resetBootstrapFrameCheckedSafe);
  if (initFormula == nullptr) {
    return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
  }

  // PDR still establishes convergence through its own frame/blocking loop, but
  // it may use validated state-correspondence equalities as a frame invariant.
  // Those equalities come from the shared SEC extraction/reset analysis and are
  // checked for init coverage and transition preservation before use.
  BoolExpr* frameInvariant =
      selectPdrFrameInvariant(problem_, initFormula, solverType_);
  const bool exactFrameClauses = useExactFrameClauses_;
  const size_t badCubeStateLimit = effectivePreciseBadCubeStateLimit(
      problem_,
      preciseBadCubeStateLimit_,
      useExactResetFrontierChecks_);
  // Bad-state queries decide whether the current frontier still contains a
  // property violation. When SEC/PDR repair learns many tiny reset-conflict
  // blockers, a projected frame view can hide exactly those blockers behind
  // unrelated clauses and make PDR rediscover stale bad cubes. Keep only the
  // bad query exact; predecessor queries below remain projected.
  const bool exactBadQueryFrameClauses =
      exactFrameClauses || learnValidatedBadFormulaClauses_;
  const bool exactPropagationFrameClauses =
      exactFrameClauses || learnValidatedBadFormulaClauses_;
  const bool guardRepeatedProjectedBadCubes =
      problem_.usesDualRailStateEncoding && !exactBadQueryFrameClauses;
  const size_t repeatedProjectedBadCubeLimit =
      maxRepeatedProjectedBadCubeHits();
  std::optional<StateCube> previousProjectedBadCube;
  size_t previousProjectedBadCubeLevel = 0;
  size_t repeatedProjectedBadCubeHits = 0;

  TransitionExprResolver transitionByState(problem_);
  ComplementPartnerIndex complementPartners(problem_);
  PdrFormulaSupportCache formulaSupportCache(problem_.dualRailStatePairs);
  // The bad predicate is the same for every frame query. Cache its state
  // support once so repeated PDR bad-cube checks do not rebuild the large
  // combined miter state set on every loop iteration.
  const auto preciseBadStateSupport = collectBoundedStateSupportSymbols(
      problem_.bad,
      kMaxPreciseBadCubeSupportNodes,
      badCubeStateLimit,
      transitionByState.stateSymbols());
  ResetFrontierCache resetFrontierCache;
  importProcessResetUnreachableCores(problem_, resetFrontierCache, frameInvariant);
  BadCubeAssumptionCache badCubeAssumptionCache;
  PredecessorAssumptionCache predecessorAssumptionCache;
  LargeDualRailPdrTransientCacheReleaseGuard cacheReleaseGuard{
      resetFrontierCache,
      badCubeAssumptionCache,
      predecessorAssumptionCache,
      formulaSupportCache,
      problem_,
      frameInvariant};
  size_t remainingPredecessorQueries = effectiveMaxPredecessorQueries;
  size_t* predecessorQueryBudget =
      effectiveMaxPredecessorQueries == 0 ? nullptr : &remainingPredecessorQueries;
  size_t remainingProjectedCounterexampleRefinements =
      effectiveMaxProjectedCounterexampleRefinements;
  size_t* projectedCounterexampleRefinementBudget =
      effectiveMaxProjectedCounterexampleRefinements == 0
          ? nullptr
          : &remainingProjectedCounterexampleRefinements;
  std::vector<FrameClauses> frames(1);
  emitPdrTraceFrames("initial_frames", frames);

  // Before growing any frame sequence, check whether Init itself already
  // contains a bad state.
  if (!(problem_.resetBootstrapCycles != 0 && resetBootstrapFrameCheckedSafe)) {
    if (auto badCube = findBadCube(
            problem_,
            solverType_,
            initFormula,
            frameInvariant,
            frames,
            preciseBadStateSupport,
            badCubeStateLimit,
            transitionByState.stateSymbols(),
            0,
            complementPartners,
            exactBadQueryFrameClauses,
            &badCubeAssumptionCache,
            &formulaSupportCache);
        badCube.has_value()) {
      emitPdrTrace("bad_cube@F0", formatCubeForPdrTrace(*badCube));
      return {PDRStatus::Different, 0};
    }
    if (hasPdrBudgetExhaustion()) {
      return {PDRStatus::Inconclusive, 0};  // LCOV_EXCL_LINE
    }
  }

  if (maxFrames == 0) {
    return {PDRStatus::Inconclusive, 0};
  }

  // Init/bootstrap facts are static for a PDR run. Wide dual-rail SEC problems
  // can carry tens of thousands of boot assignments, so build the lookup index
  // once instead of rebuilding it for every blocked obligation.
  const InitFactIndex initFacts = buildInitFactIndex(problem_);
  const auto seedClauses = buildSeedClauses(problem_, initFacts);
  frames.emplace_back(FrameClauses{seedClauses});
  seedImportedResetPredecessorClauses(frames, resetFrontierCache);
  emitPdrTraceFrames("seeded_frames", frames);
  for (size_t level = 1; level <= maxFrames; ++level) {
    // Phase 1: exhaust the proof obligations created by bad states that still
    // survive in the current frontier.
    while (true) {
      const auto badCube =
          findBadCube(
              problem_,
              solverType_,
              initFormula,
              frameInvariant,
              frames,
              preciseBadStateSupport,
              badCubeStateLimit,
              transitionByState.stateSymbols(),
              level,
              complementPartners,
              exactBadQueryFrameClauses,
              &badCubeAssumptionCache,
              &formulaSupportCache);
      if (hasPdrBudgetExhaustion()) {
        return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
      }
      if (!badCube.has_value()) {
        break;
      }
      if (guardRepeatedProjectedBadCubes) {
        if (previousProjectedBadCube.has_value() &&
            previousProjectedBadCubeLevel == level &&
            *previousProjectedBadCube == *badCube) {
          ++repeatedProjectedBadCubeHits; // LCOV_EXCL_LINE
        } else { // LCOV_EXCL_LINE
          previousProjectedBadCube = *badCube;
          previousProjectedBadCubeLevel = level;
          repeatedProjectedBadCubeHits = 1;
        }
        if (repeatedProjectedBadCubeHits > repeatedProjectedBadCubeLimit) {
          if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
            emitSecDiag(  // LCOV_EXCL_LINE
                "SEC PDR stats: repeated projected bad cube exhausted ",
                "limit=", repeatedProjectedBadCubeLimit,
                " level=", level,
                " cube=", badCube->size(), // LCOV_EXCL_LINE
                " hash=", cubeFingerprint(*badCube)); // LCOV_EXCL_LINE
          }  // LCOV_EXCL_LINE
          markPdrBudgetExhausted( // LCOV_EXCL_LINE
              PdrBudgetExhaustion::RepeatedProjectedBadCube);  // LCOV_EXCL_LINE
          return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
        }
      }
      emitPdrTrace(("bad_cube@F" + std::to_string(level)).c_str(),
                   formatCubeForPdrTrace(*badCube));
      size_t badFrame = level;
      if (!blockProofObligations(
              problem_,
              solverType_,
              transitionByState,
              initFormula,
              frameInvariant,
              frames,
              initFacts,
              *badCube,
              level,
              badFrame,
              complementPartners,
              effectivePredecessorProjectionLimit,
              exactFrameClauses,
              refineProjectedCounterexamples_,
              resetFrontierCache,
              predecessorAssumptionCache,
              maxBoundedRootGeneralizationAttempts_,
              learnValidatedBadFormulaClauses_,
              useExactResetFrontierChecks_,
              predecessorQueryBudget,
              projectedCounterexampleRefinementBudget,
              &formulaSupportCache)) {
        if (hasPdrBudgetExhaustion()) {
          return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
        }
        emitPdrTraceFrames("frames_before_counterexample", frames);
        return {PDRStatus::Different, badFrame};
      }
      if (hasPdrBudgetExhaustion()) {
        return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
      }
      emitPdrTraceFrames("frames_after_blocking", frames);
    }

    // Phase 2: create the next frame, seed it with already-known startup
    // facts
    frames.emplace_back(FrameClauses{seedClauses});
    // and then push learned clauses forward.
    // We push in order to reach covergence and the condition is that that 
    // the clause is not preventing an actual bad path
    propagateClauses(
        problem_,
        solverType_,
        transitionByState,
        initFormula,
        frameInvariant,
        frames,
        level,
        complementPartners,
        effectivePredecessorProjectionLimit,
        exactPropagationFrameClauses,
        &predecessorAssumptionCache,
        predecessorQueryBudget,
        &formulaSupportCache);
    if (hasPdrBudgetExhaustion()) {
      return {PDRStatus::Inconclusive, level};  // LCOV_EXCL_LINE
    }
    emitPdrTraceFrames(("frames_after_propagation@F" + std::to_string(level)).c_str(),
                       frames);

    // Phase 3: convergence means F[i] == F[i+1], so the frame has become an
    // inductive invariant and the SEC property is proved.
    for (size_t convergenceLevel = 1; convergenceLevel <= level; ++convergenceLevel) {
      if (framesConverged(frames[convergenceLevel], frames[convergenceLevel + 1])) {
        emitPdrTraceFrames(
            ("frames_converged@F" + std::to_string(convergenceLevel)).c_str(), frames);
        return {PDRStatus::Equivalent, convergenceLevel};
      }
    }
  }
  if (pdrStatsEnabled()) {  // LCOV_EXCL_LINE
    emitSecDiag(  // LCOV_EXCL_LINE
        "SEC PDR stats: max frame budget exhausted max_frames=",
        maxFrames);
  }  // LCOV_EXCL_LINE
  return {PDRStatus::Inconclusive, maxFrames};  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC

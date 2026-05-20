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

#include "common/BoolExprUtils.h"
#include "common/ProofProblemDebug.h"
#include "common/SecDiag.h"
#include "kinduction/BaseCaseSolver.h"
#include "proof/ProofEngineShared.h"
#include "proof/TransitionExprResolver.h"
#include "kinduction/SatEncoding.h"

namespace KEPLER_FORMAL::SEC {

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
constexpr size_t kMaxResetSymbolicCheapEvalNodes = 128;
// BlackParrot sampling showed deep concrete validation repeatedly disproving
// the same two-literal reset core, then falling into the exact reset-frontier
// BMC builder only because the symbolic reset-image traversal hit its generic
// shortcut budget at target_step=7.  Keep the larger budget restricted to tiny
// cores: the later SAT proof is still independently support/resource capped.
constexpr size_t kMaxDeepSmallCubeResetSymbolicEvaluatorStates = 1048576;
constexpr size_t kMaxDeepSmallCubeResetSymbolicEvaluatorExprs = 8388608;
constexpr size_t kMaxDeepSmallCubeResetSymbolicLiterals = 2;
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
constexpr size_t kMaxPreciseBadCubeSupportNodes = 16384;
// After exact BMC rejects an abstract final-stage PDR counterexample, a small
// state-only bad predicate can be turned into frame clauses directly. Keep the
// enumeration deliberately small: this is for one-output ASIC cones such as
// BlackParrot's six-state-bit bad predicates, not arbitrary datapath CNF.
constexpr size_t kMaxValidatedBadFormulaCnfSupport = 8;
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
constexpr long long kTargetResetFrontierBadFormulaConflictLimit = 2000;
constexpr long long kTargetResetFrontierBadFormulaPropagationLimit = 50000;
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
// assignments may remain. A later BlackParrot sample caught this optional
// residual batch spending the wall in assumption solving, so keep this
// path disabled and let ordinary PDR/root-cube validation populate exact cores
// only for candidates it actually needs.
constexpr size_t kMaxResidualExactResetCubeValidatedBadFormulaClauses = 0;
constexpr size_t kMaxResidualExactResetCubeValidatedBadFormulaFrame = 5;
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
// the same predecessor SAT query, but we first try removing large literal
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
constexpr size_t kMaxCadicalExactResetPrecheckTransitionSupport = 4096;
constexpr size_t kDefaultPdrStatsInterval = 1000;
constexpr size_t kInitialPdrStatsQueries = 20;
// PDR can use inferred state correspondences as an ordinary frame invariant,
// but ASIC retiming/optimization can make a few inferred pairs non-inductive
// while many others are still valid and very useful.  Mine a validated subset
// once per PDR run instead of forcing the blocking loop to rediscover thousands
// of those equality clauses one cube at a time.
constexpr size_t kMaxStateEqualitySubsetPairs = 2048;
constexpr size_t kMaxStateEqualitySubsetIterations = 256;

// Cubes represent a concrete bad/predecessor state, while clauses are the
// blocked generalization of such a state stored in a PDR frame.
struct CubeLiteral {
  size_t symbol = 0;
  bool value = false;

  bool operator==(const CubeLiteral& other) const {
    return symbol == other.symbol && value == other.value;
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

struct ObservedOutputBadClauseGroup {
  size_t outputIndex = 0;
  BoolExpr* outputBad = nullptr;
  std::vector<StateClause> clauses;
};

struct FrameClauses {
  // F[i] stores clauses known to hold for all states reachable within i steps.
  std::vector<StateClause> clauses;
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
    const bool parity = parityToParent_.at(symbol);
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
    ensureSymbol(symbol);
    const size_t parent = parent_[symbol];
    const bool parity = parityToParent_[symbol];
    if (parent == symbol) {
      return {symbol, false};
    }
    const auto root = mutableFind(parent);
    parent_[symbol] = root.first;
    parityToParent_[symbol] = parity ^ root.second;
    return {parent_[symbol], parityToParent_[symbol]};
  }

  void unite(size_t lhs, size_t rhs, bool inverted) {
    const auto lhsRoot = mutableFind(lhs);
    const auto rhsRoot = mutableFind(rhs);
    if (lhsRoot.first == rhsRoot.first) {
      return;
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

class ResetSymbolicEvaluator;
class ResetExpressionCanonicalizer;
struct ResetBootstrapExpressionRelations;

struct ResetFrontierCache {
  // PDR can revisit the same abstract F[0] cube through multiple bad
  // obligations. Cache the exact reset-image answer so we do not rebuild the
  // same reset-prefix SAT query more than once per engine run.
  std::unordered_map<std::string, bool> outsideByCubeKey;
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
  std::unordered_map<std::string, bool> transitionImpossibleResetCoreByKey;
  std::vector<StateCube> transitionImpossibleResetCores;
  // Reset-expression conflict proofs are local to a target post-reset step and
  // cube. Validated bad-formula repair asks many overlapping pair/triple/full
  // cube questions, so memoize both proved conflicts and misses.
  std::unordered_map<std::string, ResetExpressionConflictMemoEntry>
      resetExpressionConflictByKey;
  // Once a deep reset-expression shortcut is rejected for budget/support, later
  // deeper frames should not rebuild the same huge optional reset cone.
  std::unordered_map<std::string, size_t> resetExpressionBudgetSkipFromStep;
  // Deep single-output bad-formula validation is an exact proof, but it can be
  // expensive. If it fails to prove unreachable for a given local bad CNF, do
  // not retry the same proof every time PDR rediscovers a neighboring root.
  std::unordered_set<std::string> wholeBadFormulaValidationMisses;
};

enum class ConcreteCubeReachabilityMode {
  CachedAssumptions,
  OneShotUnitClauses,
};

class PdrQueryBudgetExceeded : public std::runtime_error {
 public:
  PdrQueryBudgetExceeded()
      : std::runtime_error("PDR predecessor query budget exceeded") {}
};

void consumePdrPredecessorQueryBudget(size_t* remainingQueries) {
  if (remainingQueries == nullptr) {
    return;
  }
  if (*remainingQueries == 0) {
    throw PdrQueryBudgetExceeded();
  }
  --(*remainingQueries);
}

bool pdrStatsEnabled() {
  return std::getenv("KEPLER_SEC_PDR_STATS") != nullptr;
}

bool pdrResetShortcutDiagEnabled() {
  return std::getenv("KEPLER_SEC_PDR_RESET_SHORTCUT_DIAG") != nullptr;
}

std::string_view concreteCubeReachabilityModeName(
    ConcreteCubeReachabilityMode mode) {
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
    return kDefaultPdrStatsInterval;
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
                                            unsigned defaultValue) {
  const char* valueText = std::getenv(name);
  if (valueText == nullptr || *valueText == '\0') {
    return defaultValue;
  }
  const auto value = std::strtoull(valueText, nullptr, 10);
  return value > std::numeric_limits<unsigned>::max()
             ? std::numeric_limits<unsigned>::max()
             : static_cast<unsigned>(value);
}

unsigned resetExpressionProofConflictLimit() {
  return envUnsignedLimitOrDefaultAllowZero(
      "KEPLER_SEC_PDR_RESET_EXPRESSION_CONFLICT_LIMIT",
      kDefaultResetExpressionProofConflictLimit);
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

bool shouldEmitPdrStats(size_t queryNumber) {
  if (!pdrStatsEnabled()) {
    return false;
  }
  return queryNumber <= kInitialPdrStatsQueries ||
         queryNumber % pdrStatsInterval() == 0;
}

void addComplementedStateRelations(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    size_t numFrames);

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame);

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame);

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame);

void addPostBootstrapResetInputConstraints(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const KInductionProblem& problem,
    size_t frame);

void addFormulaSymbols(BoolExpr* formula, std::unordered_set<size_t>& symbols);

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output);

bool predecessorSourceFrameIsKnownSafe(size_t level);

void normalizeCube(StateCube& cube);

std::optional<std::set<size_t>> boundedSupportVars(BoolExpr* formula,
                                                   size_t maxVisitedNodes);

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols);

std::unordered_map<size_t, BoolExpr*> buildTransitionExprByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, BoolExpr*> transitionExprByStateSymbol;
  transitionExprByStateSymbol.reserve(
      problem.transitions0.size() + problem.transitions1.size());
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    transitionExprByStateSymbol.emplace(stateSymbol, expr);
  }
  return transitionExprByStateSymbol;
}

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
    BoolExpr* frameInvariant);

ResetFrontierReachabilityContext& resetReachabilityContextFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant);

std::unordered_map<size_t, size_t> buildComplementPrimaryByStateSymbol(
    const KInductionProblem& problem) {
  std::unordered_map<size_t, size_t> primaryByComplement;
  primaryByComplement.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);  // LCOV_EXCL_LINE
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    primaryByComplement.emplace(complementedSymbol, primarySymbol);
  }
  return primaryByComplement;
}

std::vector<size_t> sortUniqueSymbols(std::unordered_set<size_t> symbols) {
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
    return {};  // LCOV_EXCL_LINE
  }

  const auto support = boundedSupportVars(formula, maxVisitedNodes);
  if (!support.has_value()) {
    return std::nullopt;
  }

  std::unordered_set<size_t> stateSupport;
  for (const auto symbol : *support) {
    if (stateSymbolSet.find(symbol) != stateSymbolSet.end()) {
      stateSupport.insert(symbol);
      if (stateSupport.size() > maxStateSymbols) {
        return std::nullopt;
      }
    }
  }
  return sortUniqueSymbols(std::move(stateSupport));
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const std::unordered_map<size_t, BoolExpr*>& transitionExprByStateSymbol) {
  const auto primaryByComplement = buildComplementPrimaryByStateSymbol(problem);
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionExprByStateSymbol.find(symbol) !=
        transitionExprByStateSymbol.end()) {
      targets.insert(symbol);
      continue;
    }

    // Complemented flop outputs are constrained through the primary flop. If a
    // cube talks only about the complemented bit, encode the primary transition
    // and let the complemented-state relation connect the two next-frame bits.
    if (const auto primaryIt = primaryByComplement.find(symbol);  // LCOV_EXCL_LINE
        primaryIt != primaryByComplement.end() &&  // LCOV_EXCL_LINE
        transitionExprByStateSymbol.find(primaryIt->second) !=  // LCOV_EXCL_LINE
            transitionExprByStateSymbol.end()) {  // LCOV_EXCL_LINE
      targets.insert(primaryIt->second);  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> expandTransitionTargets(
    const KInductionProblem& problem,
    const std::vector<size_t>& requestedTargets,
    const TransitionExprResolver& transitionByState) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::unordered_set<size_t> targets;
  targets.reserve(requestedTargets.size());

  for (const auto symbol : requestedTargets) {
    if (transitionByState.contains(symbol)) {
      targets.insert(symbol);
      continue;
    }
    if (const auto primaryIt = primaryByComplement.find(symbol);
        primaryIt != primaryByComplement.end() &&
        transitionByState.contains(primaryIt->second)) {
      targets.insert(primaryIt->second);
    }
  }

  return sortUniqueSymbols(std::move(targets));
}

std::vector<size_t> collectTransitionSupportSymbols(
    const TransitionExprResolver& transitionByState,
    const std::vector<size_t>& encodedTargets) {
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
    return 0;
  }
  size_t estimate = 0;
  for (const auto stateSymbol : encodedTargets) {
    estimate += transitionByState.nodeCount(stateSymbol);
  }
  return estimate;
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
  groups.push_back(std::move(group));
}

std::vector<TransitionEncodingLiteralGroup> groupTransitionCubeLiteralsBySymbolMap(
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube) {
  const auto& primaryByComplement = transitionByState.primaryByComplement();
  std::vector<TransitionEncodingLiteralGroup> groups;
  groups.reserve(3);
  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);
      if (primaryIt == primaryByComplement.end() ||
          !transitionByState.contains(primaryIt->second)) {
        continue;
      }
      transitionSymbol = primaryIt->second;
      desiredValue = !desiredValue;
    }

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

std::vector<size_t> cubeStateSymbols(const StateCube& cube) {
  std::unordered_set<size_t> symbols;
  symbols.reserve(cube.size());
  for (const auto& literal : cube) {
    symbols.insert(literal.symbol);
  }
  return sortUniqueSymbols(std::move(symbols));
}

std::vector<size_t> boundedPrefixSymbols(const std::vector<size_t>& symbols,
                                         size_t limit) {
  if (limit == 0 || symbols.size() <= limit) {
    return symbols;
  }
  return std::vector<size_t>(symbols.begin(), symbols.begin() + limit);
}

StateCube boundedPrefixCube(const StateCube& cube, size_t limit) {
  if (limit == 0 || cube.size() <= limit) {
    return cube;
  }
  return StateCube(cube.begin(), cube.begin() + limit);
}

size_t transitionLiteralCost(const TransitionExprResolver& transitionByState,
                             size_t symbol) {
  size_t transitionSymbol = symbol;
  if (!transitionByState.contains(transitionSymbol)) {
    const auto primaryIt = transitionByState.primaryByComplement().find(symbol);
    if (primaryIt == transitionByState.primaryByComplement().end() ||
        !transitionByState.contains(primaryIt->second)) {
      return 0;
    }
    transitionSymbol = primaryIt->second;
  }
  // Support width is the dominant SAT-query cost; node count breaks ties among
  // cones with similar state/input footprints.
  return transitionByState.support(transitionSymbol).size() * 4 +
         transitionByState.nodeCount(transitionSymbol);
}

size_t blockedCubeTransitionSupportSize(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube) {
  const std::vector<size_t> targetSymbols = cubeStateSymbols(cube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  return collectTransitionSupportSymbols(transitionByState, encodedTargets).size();
}

StateCube boundedCheapTransitionCube(
    const StateCube& cube,
    size_t limit,
    const TransitionExprResolver& transitionByState) {
  if (limit == 0 || cube.size() <= limit) {
    return cube;
  }

  StateCube selected = cube;
  std::stable_sort(
      selected.begin(),
      selected.end(),
      [&](const CubeLiteral& lhs, const CubeLiteral& rhs) {
        const size_t lhsCost = transitionLiteralCost(transitionByState, lhs.symbol);
        const size_t rhsCost = transitionLiteralCost(transitionByState, rhs.symbol);
        if (lhsCost != rhsCost) {
          return lhsCost < rhsCost;
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
        return lhs.value < rhs.value;
      });
}

std::string resetFrontierCacheKey(const StateCube& cube,
                                  size_t postBootstrapSteps);

void rememberPdrResetUnreachableCore(
    ResetFrontierCache& cache,
    StateCube core,
    size_t postBootstrapSteps) {
  normalizeCube(core);
  if (core.empty()) {
    return;
  }

  auto& cores =
      cache.resetUnreachableCoresByPostBootstrapStep[postBootstrapSteps];
  for (const auto& existing : cores) {
    if (cubeContainsCube(core, existing)) {
      return;
    }
  }
  cores.erase(
      std::remove_if(
          cores.begin(),
          cores.end(),
          [&](const StateCube& existing) {
            return cubeContainsCube(existing, core);
          }),
      cores.end());
  if (cores.size() >= kMaxPdrResetUnreachableCoresPerStep) {
    cores.erase(cores.begin());
  }
  cores.push_back(std::move(core));
}

void rememberTransitionImpossibleResetCore(
    ResetFrontierCache& cache,
    StateCube core) {
  normalizeCube(core);
  if (core.empty()) {
    return;
  }

  const std::string key = resetFrontierCacheKey(core, 0);
  cache.transitionImpossibleResetCoreByKey[key] = true;
  for (const auto& existing : cache.transitionImpossibleResetCores) {
    if (cubeContainsCube(core, existing)) {
      return;
    }
  }
  cache.transitionImpossibleResetCores.erase(
      std::remove_if(
          cache.transitionImpossibleResetCores.begin(),
          cache.transitionImpossibleResetCores.end(),
          [&](const StateCube& existing) {
            return cubeContainsCube(existing, core);
          }),
      cache.transitionImpossibleResetCores.end());
  cache.transitionImpossibleResetCores.push_back(std::move(core));
}

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
  }
  return std::nullopt;
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
    return;
  }

  rememberPdrResetUnreachableCore(cache, core, postBootstrapSteps);
  auto& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  rememberResetFrontierUnreachableCube(
      reachabilityContext, cubeAssignments(core), postBootstrapSteps);
}

std::optional<StateCube> findTransitionImpossibleResetCoreForCube(
    const ResetFrontierCache& cache,
    const StateCube& cube) {
  for (const auto& core : cache.transitionImpossibleResetCores) {
    if (cubeContainsCube(cube, core)) {
      return core;
    }
  }
  return std::nullopt;
}

std::string resetFrontierCacheKey(const StateCube& cube,
                                  size_t postBootstrapSteps) {
  // Several PDR paths derive equivalent root cubes from different obligation
  // sources. Canonicalize here so exact reset-frontier answers are reusable
  // even if a caller hands us the same literals in a different order.
  StateCube normalizedCube = cube;
  normalizeCube(normalizedCube);
  std::string key = std::to_string(postBootstrapSteps);
  key.push_back('|');
  for (const auto& literal : normalizedCube) {
    key += std::to_string(literal.symbol);
    key.push_back(literal.value ? '1' : '0');
    key.push_back(';');
  }
  return key;
}

std::string resetExpressionConflictCacheKey(const StateCube& cube,
                                            size_t targetStep,
                                            BoolExpr* frameInvariant) {
  std::string key = resetFrontierCacheKey(cube, targetStep);
  key.push_back('|');
  std::ostringstream oss;
  oss << static_cast<const void*>(frameInvariant);
  key += oss.str();
  return key;
}

std::string resetExpressionBudgetSkipKey(const StateCube& cube,
                                         BoolExpr* frameInvariant) {
  (void)frameInvariant;
  std::string key = resetFrontierCacheKey(cube, 0);
  return key;
}

bool resetExpressionBudgetSkipApplies(
    const std::unordered_map<std::string, size_t>& skipFromStep,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant) {
  const auto it =
      skipFromStep.find(resetExpressionBudgetSkipKey(cube, frameInvariant));
  return it != skipFromStep.end() && it->second <= targetStep;
}

void rememberResetExpressionBudgetSkip(
    std::unordered_map<std::string, size_t>& skipFromStep,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant) {
  const std::string key = resetExpressionBudgetSkipKey(cube, frameInvariant);
  const auto [it, inserted] = skipFromStep.emplace(key, targetStep);
  if (!inserted && targetStep < it->second) {
    it->second = targetStep;
  }
}

const ResetExpressionConflictMemoEntry* lookupResetExpressionConflictMemo(
    const std::unordered_map<std::string, ResetExpressionConflictMemoEntry>& memo,
    const std::string& key) {
  const auto it = memo.find(key);
  if (it == memo.end()) {
    return nullptr;
  }
  return &it->second;
}

void rememberResetExpressionConflictMemo(
    std::unordered_map<std::string, ResetExpressionConflictMemoEntry>& memo,
    const std::string& key,
    const std::optional<StateCube>& conflict) {
  ResetExpressionConflictMemoEntry entry;
  entry.hasConflict = conflict.has_value();
  if (conflict.has_value()) {
    entry.conflict = *conflict;
  }
  memo[key] = std::move(entry);
}

std::string stateClauseKey(const StateClause& clause) {
  // Learned-frame clauses are normalized before storage. A compact textual key
  // is enough here and keeps the local projected-frame CEGAR loop independent
  // from any lossy hash/fingerprint collision behavior.
  std::string key;
  for (const auto& literal : clause) {
    key += std::to_string(literal.symbol);
    key.push_back(literal.positive ? '1' : '0');
    key.push_back(';');
  }
  return key;
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

std::string formatCubeForDiag(const StateCube& cube) {
  std::ostringstream oss;
  oss << "{";
  for (size_t i = 0; i < cube.size(); ++i) {
    if (i != 0) {
      oss << ",";
    }
    oss << cube[i].symbol << "=" << (cube[i].value ? "1" : "0");
  }
  oss << "}";
  return oss.str();
}

std::optional<SymbolPair> simpleVariableEqualityPair(BoolExpr* expr) {
  if (expr == nullptr || expr->getOp() != Op::NOT) {
    return std::nullopt;
  }
  BoolExpr* xorExpr = expr->getLeft();
  if (xorExpr == nullptr || xorExpr->getOp() != Op::XOR) {
    return std::nullopt;
  }
  BoolExpr* lhs = xorExpr->getLeft();
  BoolExpr* rhs = xorExpr->getRight();
  if (lhs == nullptr || rhs == nullptr ||
      lhs->getOp() != Op::VAR || rhs->getOp() != Op::VAR ||
      lhs->getId() < 2 || rhs->getId() < 2 ||
      lhs->getId() == rhs->getId()) {
    return std::nullopt;
  }
  SymbolPair pair{lhs->getId(), rhs->getId()};
  if (pair.second < pair.first) {
    std::swap(pair.first, pair.second);
  }
  return pair;
}

std::vector<std::pair<size_t, size_t>> collectSimpleVariableEqualities(
    BoolExpr* formula) {
  std::vector<std::pair<size_t, size_t>> equalities;
  if (formula == nullptr) {
    return equalities;
  }

  std::unordered_set<SymbolPair, SymbolPairHash> seen;
  std::vector<BoolExpr*> stack{formula};
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (node == nullptr) {
      continue;  // LCOV_EXCL_LINE
    }
    if (node->getOp() == Op::AND) {
      stack.push_back(node->getLeft());
      stack.push_back(node->getRight());
      continue;
    }
    if (const auto pair = simpleVariableEqualityPair(node);
        pair.has_value() && seen.insert(*pair).second) {
      equalities.emplace_back(pair->first, pair->second);
    }
  }
  return equalities;
}

std::optional<std::set<size_t>> boundedSupportVars(BoolExpr* formula,
                                                   size_t maxVisitedNodes) {
  if (formula == nullptr) {
    return std::set<size_t>{};  // LCOV_EXCL_LINE
  }

  std::set<size_t> support;
  std::unordered_set<const BoolExpr*> visited;
  std::vector<const BoolExpr*> stack{formula};
  while (!stack.empty()) {
    const BoolExpr* node = stack.back();
    stack.pop_back();
    if (!visited.insert(node).second) {
      continue;
    }
    if (visited.size() > maxVisitedNodes) {
      return std::nullopt;
    }

    if (node->getOp() == Op::VAR) {
      support.insert(node->getId());
      continue;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return support;
}

class ResetConstantEvaluator {
 public:
  ResetConstantEvaluator(const KInductionProblem& problem,
                         const TransitionExprResolver& transitionByState)
      : problem_(problem),
        transitionByState_(transitionByState),
        exprMemoByStep_(problem.resetBootstrapCycles + 1) {
    resetInputs_.reserve(problem.resetBootstrapInputs.size());
    for (const auto& [symbol, value] : problem.resetBootstrapInputs) {
      resetInputs_.emplace(symbol, value);
    }
    initialStates_.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      initialStates_.emplace(symbol, value);
    }
    bootstrapStates_.reserve(problem.bootstrapStateAssignments.size());
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      bootstrapStates_.emplace(symbol, value);
    }
  }

  std::optional<bool> stateValue(size_t symbol, size_t step) {
    if (budgetExhausted_) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (step == problem_.resetBootstrapCycles) {
      if (const auto it = bootstrapStates_.find(symbol);
          it != bootstrapStates_.end()) {
        return it->second;
      }
    }

    const SymbolPair key{symbol, step};
    if (const auto it = stateMemo_.find(key); it != stateMemo_.end()) {
      return it->second;
    }
    if (++stateEvaluations_ > kMaxResetConstantEvaluatorStates) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    std::optional<bool> value;
    if (step == 0) {
      if (const auto it = initialStates_.find(symbol);
          it != initialStates_.end()) {
        value = it->second;
      }
    } else if (transitionByState_.contains(symbol)) {
      // A state bit at reset step N is obtained by evaluating its transition
      // expression in reset step N-1. This recursively follows only the cube's
      // required reset cone and short-circuits through reset mux constants.
      value = exprValue(transitionByState_.at(symbol), step - 1);
    }

    stateMemo_.emplace(key, value);
    return value;
  }

  bool budgetExhausted() const { return budgetExhausted_; }

  void resetBudget() {
    stateEvaluations_ = 0;
    exprEvaluations_ = 0;
    budgetExhausted_ = false;
  }

 private:
  std::optional<bool> exprValue(BoolExpr* expr, size_t step) {
    if (budgetExhausted_ || expr == nullptr || step >= exprMemoByStep_.size()) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    auto& memo = exprMemoByStep_[step];
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;
    }
    if (++exprEvaluations_ > kMaxResetConstantEvaluatorExprs) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    std::optional<bool> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          value = expr->getId() == 1;
        } else if (const auto resetIt = resetInputs_.find(expr->getId());
                   resetIt != resetInputs_.end()) {
          value = resetIt->second;
        } else {
          const auto& stateSymbols = transitionByState_.stateSymbols();
          if (stateSymbols.find(expr->getId()) != stateSymbols.end()) {
            value = stateValue(expr->getId(), step);
          }
        }
        break;
      case Op::NOT:
        if (const auto operand = exprValue(expr->getLeft(), step);
            operand.has_value()) {
          value = !*operand;
        }
        break;
      case Op::AND: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && !*lhs) {
          value = false;
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && !*rhs) {
          value = false;
        } else if (lhs.has_value() && rhs.has_value()) {
          value = *lhs && *rhs;
        }
        break;
      }
      case Op::OR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && *lhs) {
          value = true;
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && *rhs) {
          value = true;
        } else if (lhs.has_value() && rhs.has_value()) {
          value = *lhs || *rhs;
        }
        break;
      }
      case Op::XOR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        const auto rhs = exprValue(expr->getRight(), step);
        if (lhs.has_value() && rhs.has_value()) {
          value = *lhs != *rhs;
        }
        break;
      }
      case Op::NONE:
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
  std::unordered_map<size_t, bool> bootstrapStates_;
  std::unordered_map<SymbolPair, std::optional<bool>, SymbolPairHash> stateMemo_;
  std::vector<std::unordered_map<BoolExpr*, std::optional<bool>>> exprMemoByStep_;
  size_t stateEvaluations_ = 0;
  size_t exprEvaluations_ = 0;
  bool budgetExhausted_ = false;
};

std::optional<StateCube> resetSpecializedConstantConflictCube(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube) {
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

class ResetSymbolicEvaluator {
 public:
  ResetSymbolicEvaluator(const KInductionProblem& problem,
                         const TransitionExprResolver& transitionByState)
      : problem_(problem),
        transitionByState_(transitionByState),
        exprMemoByStep_(problem.resetBootstrapCycles + 1) {
    resetInputs_.reserve(problem.resetBootstrapInputs.size());
    for (const auto& [symbol, value] : problem.resetBootstrapInputs) {
      resetInputs_.emplace(symbol, value);
    }
    initialStates_.reserve(problem.initialStateAssignments.size());
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      initialStates_.emplace(symbol, value);
    }
    bootstrapStates_.reserve(problem.bootstrapStateAssignments.size());
    for (const auto& [symbol, value] : problem.bootstrapStateAssignments) {
      bootstrapStates_.emplace(symbol, value);
    }
  }

  std::optional<BoolExpr*> stateExpr(size_t symbol, size_t step) {
    if (budgetExhausted_) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (step == problem_.resetBootstrapCycles) {
      if (const auto it = bootstrapStates_.find(symbol);
          it != bootstrapStates_.end()) {
        return it->second ? BoolExpr::createTrue() : BoolExpr::createFalse();
      }
    }

    const SymbolPair key{symbol, step};
    if (const auto it = stateMemo_.find(key); it != stateMemo_.end()) {
      return it->second;
    }
    if (++stateEvaluations_ > stateEvaluationLimit_) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    BoolExpr* result = nullptr;
    if (step == 0) {
      if (const auto it = initialStates_.find(symbol);
          it != initialStates_.end()) {
        result = it->second ? BoolExpr::createTrue() : BoolExpr::createFalse();
      } else {
        result = BoolExpr::Var(symbol);
      }
    } else if (transitionByState_.contains(symbol)) {
      const auto value = exprValue(transitionByState_.at(symbol), step - 1);
      if (!value.has_value()) {
        return std::nullopt;
      }
      result = *value;
    } else {
      // Missing transition information is treated as an unconstrained symbolic
      // variable.  That is conservative: it can miss a reset relation shortcut,
      // but it cannot invent one.
      result = BoolExpr::Var(symbol);
    }

    stateMemo_.emplace(key, result);
    return result;
  }

  bool budgetExhausted() const { return budgetExhausted_; }

  void resetBudget() {
    stateEvaluations_ = 0;
    exprEvaluations_ = 0;
    budgetExhausted_ = false;
  }

  size_t stateEvaluationLimit() const { return stateEvaluationLimit_; }

  size_t exprEvaluationLimit() const { return exprEvaluationLimit_; }

  void setBudgetLimits(size_t stateEvaluationLimit,
                       size_t exprEvaluationLimit) {
    stateEvaluationLimit_ = stateEvaluationLimit;
    exprEvaluationLimit_ = exprEvaluationLimit;
  }

  const std::set<size_t>* cachedSupportVars(BoolExpr* expr);

 private:
  static bool isBoolConst(BoolExpr* expr, bool value) {
    return expr == (value ? BoolExpr::createTrue() : BoolExpr::createFalse());
  }

  std::optional<BoolExpr*> cheapExprValue(
      BoolExpr* expr,
      size_t step,
      size_t& remainingBudget) const {
    if (expr == nullptr || remainingBudget == 0) {
      return std::nullopt;
    }
    --remainingBudget;

    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          return expr;
        }
        if (const auto resetIt = resetInputs_.find(expr->getId());
            resetIt != resetInputs_.end()) {
          const bool resetValue =
              step < problem_.resetBootstrapCycles
                  ? resetIt->second
                  : !resetIt->second;
          return resetValue ? BoolExpr::createTrue()
                            : BoolExpr::createFalse();
        }
        if (step == 0) {
          if (const auto it = initialStates_.find(expr->getId());
              it != initialStates_.end()) {
            return it->second ? BoolExpr::createTrue()
                              : BoolExpr::createFalse();
          }
        }
        if (step == problem_.resetBootstrapCycles) {
          if (const auto it = bootstrapStates_.find(expr->getId());
              it != bootstrapStates_.end()) {
            return it->second ? BoolExpr::createTrue()
                              : BoolExpr::createFalse();
          }
        }
        return std::nullopt;
      case Op::NOT:
        if (const auto operand =
                cheapExprValue(expr->getLeft(), step, remainingBudget);
            operand.has_value()) {
          return BoolExpr::Not(*operand);
        }
        return std::nullopt;
      case Op::AND: {
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          return BoolExpr::createFalse();
        }
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
          return BoolExpr::createFalse();
        }
        if (lhs.has_value() && rhs.has_value()) {
          return BoolExpr::And(*lhs, *rhs);
        }
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          return rhs;
        }
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          return lhs;
        }
        return std::nullopt;
      }
      case Op::OR: {
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          return BoolExpr::createTrue();
        }
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          return BoolExpr::createTrue();
        }
        if (lhs.has_value() && rhs.has_value()) {
          return BoolExpr::Or(*lhs, *rhs);
        }
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          return rhs;
        }
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
          return lhs;
        }
        return std::nullopt;
      }
      case Op::XOR: {
        const auto lhs = cheapExprValue(expr->getLeft(), step, remainingBudget);
        const auto rhs = cheapExprValue(expr->getRight(), step, remainingBudget);
        if (lhs.has_value() && rhs.has_value()) {
          return BoolExpr::Xor(*lhs, *rhs);
        }
        return std::nullopt;
      }
      case Op::NONE:
      default:
        return std::nullopt;  // LCOV_EXCL_LINE
    }
  }

  std::optional<BoolExpr*> exprValue(BoolExpr* expr, size_t step) {
    if (budgetExhausted_ || expr == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    if (step >= exprMemoByStep_.size()) {
      exprMemoByStep_.resize(step + 1);
    }

    auto& memo = exprMemoByStep_[step];
    if (const auto it = memo.find(expr); it != memo.end()) {
      return it->second;
    }
    if (++exprEvaluations_ > exprEvaluationLimit_) {
      budgetExhausted_ = true;
      return std::nullopt;  // LCOV_EXCL_LINE
    }

    size_t cheapEvalBudget = kMaxResetSymbolicCheapEvalNodes;
    if (const auto cheapValue =
            cheapExprValue(expr, step, cheapEvalBudget);
        cheapValue.has_value()) {
      memo.emplace(expr, *cheapValue);
      return *cheapValue;
    }

    std::optional<BoolExpr*> value;
    switch (expr->getOp()) {
      case Op::VAR:
        if (expr->getId() < 2) {
          value = expr;
        } else if (const auto resetIt = resetInputs_.find(expr->getId());
                   resetIt != resetInputs_.end()) {
          // Reset controls are asserted during bootstrap frames and deasserted
          // afterward.  This lets the reset-specialized proof reason about
          // post-reset candidate cubes without opening the full SAT unroll.
          const bool resetValue =
              step < problem_.resetBootstrapCycles
                  ? resetIt->second
                  : !resetIt->second;
          value = resetValue ? BoolExpr::createTrue()
                             : BoolExpr::createFalse();
        } else {
          const auto& stateSymbols = transitionByState_.stateSymbols();
          if (stateSymbols.find(expr->getId()) != stateSymbols.end()) {
            value = stateExpr(expr->getId(), step);
          } else {
            value = expr;
          }
        }
        break;
      case Op::NOT:
        if (const auto operand = exprValue(expr->getLeft(), step);
            operand.has_value()) {
          value = BoolExpr::Not(*operand);
        }
        break;
      case Op::AND: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && isBoolConst(*lhs, false)) {
          value = BoolExpr::createFalse();
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && isBoolConst(*rhs, false)) {
          value = BoolExpr::createFalse();
          break;
        }
        if (lhs.has_value() && rhs.has_value()) {
          value = BoolExpr::And(*lhs, *rhs);
        }
        break;
      }
      case Op::OR: {
        const auto lhs = exprValue(expr->getLeft(), step);
        if (lhs.has_value() && isBoolConst(*lhs, true)) {
          value = BoolExpr::createTrue();
          break;
        }
        const auto rhs = exprValue(expr->getRight(), step);
        if (rhs.has_value() && isBoolConst(*rhs, true)) {
          value = BoolExpr::createTrue();
          break;
        }
        if (lhs.has_value() && rhs.has_value()) {
          value = BoolExpr::Or(*lhs, *rhs);
        }
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
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }

    if (value.has_value()) {
      memo.emplace(expr, *value);
    }
    return value;
  }

  const KInductionProblem& problem_;
  const TransitionExprResolver& transitionByState_;
  std::unordered_map<size_t, bool> resetInputs_;
  std::unordered_map<size_t, bool> initialStates_;
  std::unordered_map<size_t, bool> bootstrapStates_;
  std::unordered_map<SymbolPair, BoolExpr*, SymbolPairHash> stateMemo_;
  std::vector<std::unordered_map<BoolExpr*, BoolExpr*>> exprMemoByStep_;
  std::unordered_map<BoolExpr*, std::set<size_t>> supportMemo_;
  std::unordered_set<BoolExpr*> supportMisses_;
  size_t stateEvaluationLimit_ = kMaxResetSymbolicEvaluatorStates;
  size_t exprEvaluationLimit_ = kMaxResetSymbolicEvaluatorExprs;
  size_t stateEvaluations_ = 0;
  size_t exprEvaluations_ = 0;
  bool budgetExhausted_ = false;
};

class ScopedResetSymbolicEvaluatorBudget {
 public:
  ScopedResetSymbolicEvaluatorBudget(ResetSymbolicEvaluator& evaluator,
                                     size_t stateEvaluationLimit,
                                     size_t exprEvaluationLimit)
      : evaluator_(evaluator),
        previousStateEvaluationLimit_(evaluator.stateEvaluationLimit()),
        previousExprEvaluationLimit_(evaluator.exprEvaluationLimit()) {
    evaluator_.setBudgetLimits(stateEvaluationLimit, exprEvaluationLimit);
    evaluator_.resetBudget();
  }

  ScopedResetSymbolicEvaluatorBudget(
      const ScopedResetSymbolicEvaluatorBudget&) = delete;
  ScopedResetSymbolicEvaluatorBudget& operator=(
      const ScopedResetSymbolicEvaluatorBudget&) = delete;

  ~ScopedResetSymbolicEvaluatorBudget() {
    evaluator_.setBudgetLimits(
        previousStateEvaluationLimit_, previousExprEvaluationLimit_);
  }

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

bool isConstExpr(BoolExpr* expr, bool value) {
  return expr == (value ? BoolExpr::createTrue() : BoolExpr::createFalse());
}

bool areComplementExprs(BoolExpr* lhs, BoolExpr* rhs) {
  return BoolExpr::Not(lhs) == rhs || BoolExpr::Not(rhs) == lhs;
}

std::optional<bool> constExprValue(BoolExpr* expr) {
  if (expr == BoolExpr::createFalse()) {
    return false;
  }
  if (expr == BoolExpr::createTrue()) {
    return true;
  }
  return std::nullopt;
}

class BoolExprEqualityIndex {
 public:
  void unite(BoolExpr* lhs, BoolExpr* rhs) {
    if (lhs == nullptr || rhs == nullptr) {
      return;  // LCOV_EXCL_LINE
    }
    BoolExpr* lhsRoot = find(lhs);
    BoolExpr* rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      return;
    }
    if (rhsRoot < lhsRoot) {
      std::swap(lhsRoot, rhsRoot);
    }
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

  std::unordered_map<BoolExpr*, BoolExpr*> parent_;
};

class BoolExprEqualityRewriter {
 public:
  void refineToFixedPoint(
      const std::vector<std::pair<BoolExpr*, BoolExpr*>>& equalities) {
    for (size_t pass = 0; pass <= equalities.size(); ++pass) {
      bool changed = false;
      memo_.clear();
      for (const auto& [lhs, rhs] : equalities) {
        changed |= unite(rewrite(lhs), rewrite(rhs));
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
        break;
      case Op::NOT:
        rewritten = BoolExpr::Not(rewrite(expr->getLeft()));
        break;
      case Op::AND:
        rewritten = BoolExpr::And(
            rewrite(expr->getLeft()), rewrite(expr->getRight()));
        break;
      case Op::OR:
        rewritten = BoolExpr::Or(
            rewrite(expr->getLeft()), rewrite(expr->getRight()));
        break;
      case Op::XOR:
        rewritten = BoolExpr::Xor(
            rewrite(expr->getLeft()), rewrite(expr->getRight()));
        break;
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }

    rewritten = find(rewritten);
    memo_.emplace(expr, rewritten);
    return rewritten;
  }

  bool inconsistent() const { return inconsistent_; }

 private:
  bool unite(BoolExpr* lhs, BoolExpr* rhs) {
    if (lhs == nullptr || rhs == nullptr) {
      return false;  // LCOV_EXCL_LINE
    }
    BoolExpr* lhsRoot = find(lhs);
    BoolExpr* rhsRoot = find(rhs);
    if (lhsRoot == rhsRoot) {
      return false;
    }
    if (const auto lhsConst = constExprValue(lhsRoot)) {
      if (const auto rhsConst = constExprValue(rhsRoot);
          rhsConst.has_value() && *lhsConst != *rhsConst) {
        inconsistent_ = true;
        return false;  // LCOV_EXCL_LINE
      }
    }

    BoolExpr* root = preferredRoot(lhsRoot, rhsRoot);
    BoolExpr* child = root == lhsRoot ? rhsRoot : lhsRoot;
    parent_[child] = root;
    memo_.clear();
    return true;
  }

  BoolExpr* find(BoolExpr* expr) {
    const auto [it, inserted] = parent_.emplace(expr, expr);
    if (inserted || it->second == expr) {
      return expr;
    }
    it->second = find(it->second);
    return it->second;
  }

  static BoolExpr* preferredRoot(BoolExpr* lhs, BoolExpr* rhs) {
    if (constExprValue(lhs).has_value()) {
      return lhs;
    }
    if (constExprValue(rhs).has_value()) {
      return rhs;
    }
    return rhs < lhs ? rhs : lhs;
  }

  std::unordered_map<BoolExpr*, BoolExpr*> parent_;
  std::unordered_map<BoolExpr*, BoolExpr*> memo_;
  bool inconsistent_ = false;
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
    return false;
  }

  std::unordered_set<BoolExpr*> visited;
  std::vector<BoolExpr*> stack;
  visited.reserve(kMaxBootstrapExpressionRewriteNodes);
  stack.reserve(equalities.size() * 2);
  for (const auto& [lhs, rhs] : equalities) {
    if (lhs != nullptr) {
      stack.push_back(lhs);
    }
    if (rhs != nullptr) {
      stack.push_back(rhs);
    }
  }
  while (!stack.empty()) {
    BoolExpr* node = stack.back();
    stack.pop_back();
    if (!visited.insert(node).second) {
      continue;
    }
    if (visited.size() > kMaxBootstrapExpressionRewriteNodes) {
      return false;
    }
    if (node->getRight() != nullptr) {
      stack.push_back(node->getRight());
    }
    if (node->getLeft() != nullptr) {
      stack.push_back(node->getLeft());
    }
  }
  return true;
}

std::optional<StateCube> findResetExpressionRelationConflict(
    const std::vector<BoolExpr*>& expressions,
    const StateCube& cube,
    BoolExprEqualityIndex* equalityIndex = nullptr) {
  for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
      const bool equivalent =
          equalityIndex != nullptr
              ? equalityIndex->equivalent(expressions[lhs], expressions[rhs])
              : expressions[lhs] == expressions[rhs];
      if (equivalent && cube[lhs].value != cube[rhs].value) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
      if (areComplementExprs(expressions[lhs], expressions[rhs]) &&
          cube[lhs].value == cube[rhs].value) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
    }
  }
  return std::nullopt;
}

bool structuralImplies(
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
    return !*lhsConst || rhs == BoolExpr::createTrue();
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
  // recursion if more Boolean identities are added.
  memo.emplace(key, false);

  bool result = false;
  if (lhs->getOp() == Op::AND) {
    // (a & b) => a, and transitively to anything either child implies.
    result = structuralImplies(lhs->getLeft(), rhs, memo, budget) ||
             structuralImplies(lhs->getRight(), rhs, memo, budget);
  } else if (lhs->getOp() == Op::OR) {
    // (a | b) => c only when both alternatives imply c.
    result = structuralImplies(lhs->getLeft(), rhs, memo, budget) &&
             structuralImplies(lhs->getRight(), rhs, memo, budget);
  } else if (lhs->getOp() == Op::NOT && rhs->getOp() == Op::NOT) {
    result = structuralImplies(rhs->getLeft(), lhs->getLeft(), memo, budget);
  }

  if (!result && rhs->getOp() == Op::AND) {
    // a => (b & c) only when a implies both conjuncts.
    result = structuralImplies(lhs, rhs->getLeft(), memo, budget) &&
             structuralImplies(lhs, rhs->getRight(), memo, budget);
  } else if (!result && rhs->getOp() == Op::OR) {
    // a => (b | c) if a implies either disjunct.
    result = structuralImplies(lhs, rhs->getLeft(), memo, budget) ||
             structuralImplies(lhs, rhs->getRight(), memo, budget);
  }

  memo[key] = result;
  return result;
}

bool structuralImplies(BoolExpr* lhs, BoolExpr* rhs) {
  std::unordered_map<ExprPair, bool, ExprPairHash> memo;
  size_t budget = 4096;
  return structuralImplies(lhs, rhs, memo, budget);
}

std::optional<StateCube> findResetExpressionImplicationConflict(
    const std::vector<BoolExpr*>& expressions,
    const StateCube& cube) {
  // Keep this shortcut cheap on large industrial cubes. It is a conservative
  // proof search: exhausting the shared budget only disables this shortcut for
  // the current cube, leaving the exact reset-frontier checks available later.
  std::unordered_map<ExprPair, bool, ExprPairHash> implicationMemo;
  size_t implicationBudget = 4096;
  for (size_t lhs = 0; lhs < cube.size(); ++lhs) {
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
      if (cube[lhs].value && !cube[rhs].value &&
          structuralImplies(
              expressions[lhs], expressions[rhs],
              implicationMemo, implicationBudget)) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
      if (cube[rhs].value && !cube[lhs].value &&
          structuralImplies(
              expressions[rhs], expressions[lhs],
              implicationMemo, implicationBudget)) {
        StateCube conflict{cube[lhs], cube[rhs]};
        normalizeCube(conflict);
        return conflict;
      }
    }
  }
  return std::nullopt;
}

class ResetExpressionCanonicalizer {
 public:
  explicit ResetExpressionCanonicalizer(const KInductionProblem& problem) {
    parent_.reserve(problem.initialStateEqualityPairs.size() * 2);
    for (const auto& [lhsSymbol, rhsSymbol] : problem.initialStateEqualityPairs) {
      unite(lhsSymbol, rhsSymbol);
    }
    for (const auto& [symbol, value] : problem.initialStateAssignments) {
      const size_t root = find(symbol);
      if (const auto it = rootAssignments_.find(root);
          it != rootAssignments_.end() && it->second != value) {
        inconsistent_ = true;
      } else {
        rootAssignments_[root] = value;
      }
    }
  }

  BoolExpr* canonicalize(BoolExpr* expr) {
    if (expr == nullptr) {
      return nullptr;  // LCOV_EXCL_LINE
    }
    if (const auto it = memo_.find(expr); it != memo_.end()) {
      return it->second;
    }

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
            result = assignment->second ? BoolExpr::createTrue()
                                        : BoolExpr::createFalse();
          } else {
            result = BoolExpr::Var(root);
          }
        }
        break;
      }
      case Op::NOT:
        result = BoolExpr::Not(canonicalize(expr->getLeft()));
        break;
      case Op::AND:
        result = canonicalAnd(
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        break;
      case Op::OR:
        result = canonicalOr(
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        break;
      case Op::XOR:
        result = BoolExpr::Xor(
            canonicalize(expr->getLeft()), canonicalize(expr->getRight()));
        break;
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }

    memo_.emplace(expr, result);
    return result;
  }

  std::optional<BoolExpr*> canonicalizeBounded(
      BoolExpr* expr,
      size_t& remainingNodes) {
    if (expr == nullptr) {
      return nullptr;  // LCOV_EXCL_LINE
    }
    if (const auto it = memo_.find(expr); it != memo_.end()) {
      return it->second;
    }
    if (remainingNodes == 0) {
      return std::nullopt;
    }
    --remainingNodes;

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
            result = assignment->second ? BoolExpr::createTrue()
                                        : BoolExpr::createFalse();
          } else {
            result = BoolExpr::Var(root);
          }
        }
        break;
      }
      case Op::NOT: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);
        if (!left.has_value()) {
          return std::nullopt;
        }
        result = BoolExpr::Not(*left);
        break;
      }
      case Op::AND: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);
        if (!left.has_value()) {
          return std::nullopt;
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);
        if (!right.has_value()) {
          return std::nullopt;
        }
        result = canonicalAnd(*left, *right);
        break;
      }
      case Op::OR: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);
        if (!left.has_value()) {
          return std::nullopt;
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);
        if (!right.has_value()) {
          return std::nullopt;
        }
        result = canonicalOr(*left, *right);
        break;
      }
      case Op::XOR: {
        auto left = canonicalizeBounded(expr->getLeft(), remainingNodes);
        if (!left.has_value()) {
          return std::nullopt;
        }
        auto right = canonicalizeBounded(expr->getRight(), remainingNodes);
        if (!right.has_value()) {
          return std::nullopt;
        }
        result = BoolExpr::Xor(*left, *right);
        break;
      }
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }

    memo_.emplace(expr, result);
    return result;
  }

  bool inconsistent() const { return inconsistent_; }

 private:
  size_t find(size_t symbol) {
    const auto [it, inserted] = parent_.emplace(symbol, symbol);
    if (inserted || it->second == symbol) {
      return symbol;
    }
    it->second = find(it->second);
    return it->second;
  }

  void unite(size_t lhsSymbol, size_t rhsSymbol) {
    size_t lhsRoot = find(lhsSymbol);
    size_t rhsRoot = find(rhsSymbol);
    if (lhsRoot == rhsRoot) {
      return;
    }
    if (rhsRoot < lhsRoot) {
      std::swap(lhsRoot, rhsRoot);
    }
    parent_[rhsRoot] = lhsRoot;
  }

  static bool binaryContains(BoolExpr* expr, Op op, BoolExpr* child) {
    return expr != nullptr && expr->getOp() == op &&
           (expr->getLeft() == child || expr->getRight() == child);
  }

  static BoolExpr* canonicalAnd(BoolExpr* lhs, BoolExpr* rhs) {
    // Absorption is the cheap Boolean equivalence that the sampled AES reset
    // cubes needed before falling into the expensive per-cube SAT query:
    // x & (x | y) == x.
    if (binaryContains(lhs, Op::OR, rhs)) {
      return rhs;
    }
    if (binaryContains(rhs, Op::OR, lhs)) {
      return lhs;
    }
    return BoolExpr::And(lhs, rhs);
  }

  static BoolExpr* canonicalOr(BoolExpr* lhs, BoolExpr* rhs) {
    // Dual absorption: x | (x & y) == x. This keeps structurally different
    // but Boolean-equivalent reset expressions aligned without invoking SAT.
    if (binaryContains(lhs, Op::AND, rhs)) {
      return rhs;
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
      cache.resetBootstrapExpressionProblem == &problem &&
      cache.resetBootstrapExpressionTransitions == &transitionByState) {
    return cache.resetBootstrapExpressionRelations.get();
  }

  auto relations = std::make_shared<ResetBootstrapExpressionRelations>();
  std::vector<std::pair<BoolExpr*, BoolExpr*>> bootstrapExprPairs;
  bootstrapExprPairs.reserve(problem.bootstrapStateEqualityPairs.size());
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.bootstrapStateEqualityPairs) {
    const auto lhsExpr =
        evaluator.stateExpr(lhsSymbol, problem.resetBootstrapCycles);
    const auto rhsExpr =
        evaluator.stateExpr(rhsSymbol, problem.resetBootstrapCycles);
    if (!lhsExpr.has_value() || !rhsExpr.has_value()) {
      if (evaluator.budgetExhausted()) {
        return nullptr;  // LCOV_EXCL_LINE
      }
      continue;
    }
    BoolExpr* lhsCanonical = canonicalizer.canonicalize(*lhsExpr);
    BoolExpr* rhsCanonical = canonicalizer.canonicalize(*rhsExpr);
    relations->index.unite(lhsCanonical, rhsCanonical);
    bootstrapExprPairs.emplace_back(lhsCanonical, rhsCanonical);
    relations->hasRelation = true;
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
    stack.push_back(expr);
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
            return false;
          }
        }
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
      case Op::NONE:
      default:
        break;  // LCOV_EXCL_LINE
    }
  }
  return true;
}

bool addSupportVars(BoolExpr* expr,
                    std::set<size_t>& support,
                    std::unordered_set<BoolExpr*>& visited) {
  return addSupportVars(
      expr, support, visited, kMaxResetSpecializedExpressionSupport);
}

std::optional<std::set<size_t>> collectSupportVars(BoolExpr* expr) {
  std::set<size_t> support;
  std::unordered_set<BoolExpr*> visited;
  if (!addSupportVars(expr, support, visited)) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  return support;
}

const std::set<size_t>* ResetSymbolicEvaluator::cachedSupportVars(
    BoolExpr* expr) {
  if (expr == nullptr) {
    return nullptr;  // LCOV_EXCL_LINE
  }
  if (const auto it = supportMemo_.find(expr); it != supportMemo_.end()) {
    return &it->second;
  }
  if (supportMisses_.find(expr) != supportMisses_.end()) {
    return nullptr;
  }

  auto support = collectSupportVars(expr);
  if (!support.has_value()) {
    supportMisses_.insert(expr);
    return nullptr;
  }
  const auto [it, _] = supportMemo_.emplace(expr, std::move(*support));
  return &it->second;
}

struct AffineXorSignature {
  bool constant = false;
  std::vector<size_t> symbols;
};

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
      }
      case Op::NOT:
        // In Boolean affine form, NOT(x) is x xor 1.
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
      case Op::NONE:
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
    for (size_t rhs = lhs + 1; rhs < cube.size(); ++rhs) {
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
        return conflict;
      }
    }
  }
  return std::nullopt;
}

bool supportsIntersect(const std::set<size_t>& lhs,
                       const std::set<size_t>& rhs) {
  auto lhsIt = lhs.begin();
  auto rhsIt = rhs.begin();
  while (lhsIt != lhs.end() && rhsIt != rhs.end()) {
    if (*lhsIt == *rhsIt) {
      return true;
    }
    if (*lhsIt < *rhsIt) {
      ++lhsIt;
    } else {
      ++rhsIt;
    }
  }
  return false;
}

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
  struct Candidate {
    BoolExpr* lhs = nullptr;
    BoolExpr* rhs = nullptr;
    std::set<size_t> support;
  };

  std::vector<Candidate> candidates;
  candidates.reserve(problem.bootstrapStateEqualityPairs.size());
  for (const auto& [lhsSymbol, rhsSymbol] :
       problem.bootstrapStateEqualityPairs) {
    const auto lhsExpr =
        evaluator.stateExpr(lhsSymbol, problem.resetBootstrapCycles);
    const auto rhsExpr =
        evaluator.stateExpr(rhsSymbol, problem.resetBootstrapCycles);
    if (!lhsExpr.has_value() || !rhsExpr.has_value()) {
      return std::nullopt;
    }
    BoolExpr* lhs = *lhsExpr;
    BoolExpr* rhs = *rhsExpr;
    if (canonicalizer != nullptr) {
      lhs = canonicalizer->canonicalize(lhs);
      rhs = canonicalizer->canonicalize(rhs);
    }

    const auto* lhsSupport = evaluator.cachedSupportVars(lhs);
    if (lhsSupport == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    const auto* rhsSupport = evaluator.cachedSupportVars(rhs);
    if (rhsSupport == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    std::set<size_t> support = *lhsSupport;
    support.insert(rhsSupport->begin(), rhsSupport->end());
    candidates.push_back({lhs, rhs, std::move(support)});
  }

  std::vector<std::pair<BoolExpr*, BoolExpr*>> selected;
  selected.reserve(candidates.size());
  std::vector<bool> used(candidates.size(), false);
  bool changed = true;
  while (changed) {
    changed = false;
    for (size_t i = 0; i < candidates.size(); ++i) {
      if (used[i] || !supportsIntersect(candidates[i].support, relevantSupport)) {
        continue;
      }
      used[i] = true;
      changed = true;
      selected.emplace_back(candidates[i].lhs, candidates[i].rhs);
      relevantSupport.insert(
          candidates[i].support.begin(), candidates[i].support.end());
      if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {
        return std::nullopt;  // LCOV_EXCL_LINE
      }
    }
  }

  return selected;
}

std::optional<std::vector<std::pair<BoolExpr*, BoolExpr*>>>
selectRelevantFrameInvariantEqualityExprs(
    BoolExpr* frameInvariant,
    ResetSymbolicEvaluator& evaluator,
    size_t targetStep,
    std::set<size_t>& relevantSupport,
    ResetExpressionCanonicalizer* canonicalizer = nullptr) {
  struct Candidate {
    BoolExpr* lhs = nullptr;
    BoolExpr* rhs = nullptr;
    std::set<size_t> support;
  };

  const auto equalityPairs = collectSimpleVariableEqualities(frameInvariant);
  std::vector<Candidate> candidates;
  candidates.reserve(equalityPairs.size());
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    const auto lhsExpr = evaluator.stateExpr(lhsSymbol, targetStep);
    const auto rhsExpr = evaluator.stateExpr(rhsSymbol, targetStep);
    if (!lhsExpr.has_value() || !rhsExpr.has_value()) {
      return std::nullopt;
    }
    BoolExpr* lhs = *lhsExpr;
    BoolExpr* rhs = *rhsExpr;
    if (canonicalizer != nullptr) {
      lhs = canonicalizer->canonicalize(lhs);
      rhs = canonicalizer->canonicalize(rhs);
    }

    const auto* lhsSupport = evaluator.cachedSupportVars(lhs);
    if (lhsSupport == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    const auto* rhsSupport = evaluator.cachedSupportVars(rhs);
    if (rhsSupport == nullptr) {
      return std::nullopt;  // LCOV_EXCL_LINE
    }
    std::set<size_t> support = *lhsSupport;
    support.insert(rhsSupport->begin(), rhsSupport->end());
    candidates.push_back({lhs, rhs, std::move(support)});
  }

  std::vector<std::pair<BoolExpr*, BoolExpr*>> selected;
  selected.reserve(candidates.size());
  std::vector<bool> used(candidates.size(), false);
  bool changed = true;
  while (changed) {
    changed = false;
    for (size_t i = 0; i < candidates.size(); ++i) {
      if (used[i] || !supportsIntersect(candidates[i].support, relevantSupport)) {
        continue;
      }
      used[i] = true;
      changed = true;
      selected.emplace_back(candidates[i].lhs, candidates[i].rhs);
      relevantSupport.insert(
          candidates[i].support.begin(), candidates[i].support.end());
      if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {
        return std::nullopt;  // LCOV_EXCL_LINE
      }
    }
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
    std::unordered_map<std::string, ResetExpressionConflictMemoEntry>* memo =
        nullptr,
    std::unordered_map<std::string, size_t>* budgetSkipFromStep = nullptr) {
  std::string memoKey;
  if (memo != nullptr) {
    memoKey = resetExpressionConflictCacheKey(cube, targetStep, frameInvariant);
    if (const auto* entry =
            lookupResetExpressionConflictMemo(*memo, memoKey)) {
      if (!entry->hasConflict) {
        return std::nullopt;
      }
      return entry->conflict;
    }
  }
  const bool deepResetExpressionStep =
      targetStep >
      problem.resetBootstrapCycles +
          kMaxResetSpecializedBadFormulaValidationFrame;
  if (deepResetExpressionStep && budgetSkipFromStep != nullptr &&
      resetExpressionBudgetSkipApplies(
          *budgetSkipFromStep, cube, targetStep, frameInvariant)) {
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression miss "
          "reason=deep_budget_skip cube=",
          cube.size(),
          " target_step=",
          targetStep,
          " support=0 initial_equalities=0 bootstrap_equalities=0 "
          "frame_invariant_equalities=0 literals=",
          formatCubeForDiag(cube),
          " hash=",
          cubeFingerprint(cube));
    }
    if (memo != nullptr) {
      rememberResetExpressionConflictMemo(*memo, memoKey, std::nullopt);
    }
    return std::nullopt;
  }

  const auto remember = [&](std::optional<StateCube> conflict)
      -> std::optional<StateCube> {
    if (memo != nullptr) {
      if (conflict.has_value()) {
        normalizeCube(*conflict);
      }
      rememberResetExpressionConflictMemo(*memo, memoKey, conflict);
    }
    return conflict;
  };
  const auto miss = [&](std::string_view reason,
                        size_t supportSize = 0,
                        size_t initialEqualityClauses = 0,
                        size_t bootstrapEqualityClauses = 0,
                        size_t frameInvariantEqualityClauses = 0)
      -> std::optional<StateCube> {
    if (deepResetExpressionStep && budgetSkipFromStep != nullptr &&
        (reason == "canonicalize_budget" ||
         reason == "raw_support_cap" ||
         reason == "support_cap" ||
         reason == "encoded_support_cap")) {
      rememberResetExpressionBudgetSkip(
          *budgetSkipFromStep, cube, targetStep, frameInvariant);
    }
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression miss reason=",
          reason,
          " cube=",
          cube.size(),
          " target_step=",
          targetStep,
          " support=",
          supportSize,
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
    return remember(std::nullopt);
  };

  if (problem.resetBootstrapCycles == 0 || cube.empty() ||
      cube.size() > kMaxResetSpecializedExpressionCube) {
    return miss("unsupported_shape");  // LCOV_EXCL_LINE
  }

  std::vector<BoolExpr*> resetExprs;
  resetExprs.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto expr = evaluator.stateExpr(literal.symbol, targetStep);
    if (!expr.has_value()) {
      return miss(evaluator.budgetExhausted() ? "state_expr_budget"
                                              : "state_expr_missing",
                  0);
    }
    resetExprs.push_back(*expr);
  }
  if (evaluator.budgetExhausted()) {
    return miss("budget");  // LCOV_EXCL_LINE
  }

  std::set<size_t> rawSupport;
  for (BoolExpr* expr : resetExprs) {
    const auto* support = evaluator.cachedSupportVars(expr);
    if (support == nullptr) {
      return miss("raw_support_cap", rawSupport.size());  // LCOV_EXCL_LINE
    }
    rawSupport.insert(support->begin(), support->end());
    if (rawSupport.size() > kMaxResetSpecializedExpressionSupport) {
      return miss("raw_support_cap", rawSupport.size());
    }
  }

  // Fold frame-0 assignments and SEC initial equality classes before any
  // support budgeting. Without this, two reset cones that differ only by
  // design0/design1 representative names look twice as wide and can hit the
  // ASIC support cap before the local SAT proof gets to see the equalities.
  ResetExpressionCanonicalizer canonicalizer(problem);
  if (canonicalizer.inconsistent()) {
    StateCube conflict = cube;
    normalizeCube(conflict);
    return remember(conflict);  // LCOV_EXCL_LINE
  }
  size_t canonicalizeBudget = kMaxDeepResetExpressionCanonicalizeNodes;
  std::vector<BoolExpr*> proofExprs;
  proofExprs.reserve(resetExprs.size());
  for (size_t i = 0; i < resetExprs.size(); ++i) {
    BoolExpr* canonical = nullptr;
    if (deepResetExpressionStep) {
      auto bounded =
          canonicalizer.canonicalizeBounded(resetExprs[i], canonicalizeBudget);
      if (!bounded.has_value()) {
        return miss("canonicalize_budget", rawSupport.size());
      }
      canonical = *bounded;
    } else {
      canonical = canonicalizer.canonicalize(resetExprs[i]);
    }
    proofExprs.push_back(canonical);
    if (isConstExpr(canonical, !cube[i].value)) {
      return remember(StateCube{cube[i]});
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
      return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
    }
  }
  const bool canonicalizeEqualityExprs =
      targetStep <=
      problem.resetBootstrapCycles +
          kMaxResetSpecializedBadFormulaValidationFrame;
  ResetExpressionCanonicalizer* equalityCanonicalizer =
      canonicalizeEqualityExprs ? &canonicalizer : nullptr;
  auto bootstrapEqualityExprs =
      selectRelevantBootstrapEqualityExprs(
          problem, evaluator, relevantSupport, equalityCanonicalizer);
  if (!bootstrapEqualityExprs.has_value()) {
    return miss(evaluator.budgetExhausted() ? "bootstrap_eq_budget"
                                            : "bootstrap_eq_missing",
                relevantSupport.size());
  }
  auto frameInvariantEqualityExprs =
      selectRelevantFrameInvariantEqualityExprs(
          frameInvariant,
          evaluator,
          targetStep,
          relevantSupport,
          equalityCanonicalizer);
  if (!frameInvariantEqualityExprs.has_value()) {
    return miss(evaluator.budgetExhausted() ? "frame_invariant_eq_budget"
                                            : "frame_invariant_eq_missing",
                relevantSupport.size(),
                0,
                bootstrapEqualityExprs->size());
  }

  std::vector<std::pair<BoolExpr*, BoolExpr*>> proofEqualityExprs;
  proofEqualityExprs.reserve(
      bootstrapEqualityExprs->size() + frameInvariantEqualityExprs->size());
  proofEqualityExprs.insert(
      proofEqualityExprs.end(),
      bootstrapEqualityExprs->begin(),
      bootstrapEqualityExprs->end());
  proofEqualityExprs.insert(
      proofEqualityExprs.end(),
      frameInvariantEqualityExprs->begin(),
      frameInvariantEqualityExprs->end());
  if (proofEqualityExprs.size() >
      kMaxResetExpressionProofRewriteEqualities) {
    return miss(
        "proof_equality_cap",
        relevantSupport.size(),
        0,
        bootstrapEqualityExprs->size(),
        frameInvariantEqualityExprs->size());
  }
  if (!proofEqualityExprs.empty()) {
    // Bootstrap equalities and the validated PDR frame invariant are exact
    // reset-image facts for this target frame.  Quotient candidate expressions
    // through them before SAT so small equality contradictions do not fall into
    // a broad reset-frontier BMC query.
    BoolExprEqualityRewriter proofRewriter;
    proofRewriter.refineToFixedPoint(proofEqualityExprs);
    if (proofRewriter.inconsistent()) {
      StateCube conflict = cube;
      normalizeCube(conflict);
      return remember(conflict);  // LCOV_EXCL_LINE
    }

    std::vector<BoolExpr*> rewrittenProofExprs;
    rewrittenProofExprs.reserve(proofExprs.size());
    bool changed = false;
    for (size_t i = 0; i < proofExprs.size(); ++i) {
      BoolExpr* rewritten = proofRewriter.rewrite(proofExprs[i]);
      rewrittenProofExprs.push_back(rewritten);
      changed |= rewritten != proofExprs[i];
      if (isConstExpr(rewritten, !cube[i].value)) {
        return remember(StateCube{cube[i]});
      }
    }
    if (changed) {
      proofExprs = std::move(rewrittenProofExprs);
      if (const auto conflict =
              findResetExpressionRelationConflict(proofExprs, cube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              cube.size(),
              "->",
              conflict->size(),
              " via=proof_rewrite hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
      if (const auto conflict =
              findResetExpressionImplicationConflict(proofExprs, cube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              cube.size(),
              "->",
              conflict->size(),
              " via=proof_rewrite_implication hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
      if (const auto conflict =
              findAffineXorRelationConflict(proofExprs, cube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              cube.size(),
              "->",
              conflict->size(),
              " via=proof_rewrite_affine_xor hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
      relevantSupport.clear();
      for (BoolExpr* expr : proofExprs) {
        const auto* support = evaluator.cachedSupportVars(expr);
        if (support == nullptr) {
          return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
        }
        relevantSupport.insert(support->begin(), support->end());
        if (relevantSupport.size() > kMaxResetSpecializedExpressionSupport) {
          return miss("support_cap", relevantSupport.size());  // LCOV_EXCL_LINE
        }
      }
    }
  }

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

  // For tiny root cubes, first try proving a two-literal reset conflict. AES
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
      size_t first = 0;
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
          expressionSupports[second].begin(), expressionSupports[second].end());
      unionSupport.insert(
          expressionSupports[third].begin(), expressionSupports[third].end());
      return unionSupport.size();
    };

    std::vector<TripleProbe> tripleProbes;
    for (size_t first = 0; first < cube.size(); ++first) {
      if (satisfiedConstantExprs[first]) {
        continue;
      }
      for (size_t second = first + 1; second < cube.size(); ++second) {
        if (satisfiedConstantExprs[second]) {
          continue;
        }
        for (size_t third = second + 1; third < cube.size(); ++third) {
          if (satisfiedConstantExprs[third]) {
            continue;
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
    std::sort(
        tripleProbes.begin(),
        tripleProbes.end(),
        [](const TripleProbe& lhs, const TripleProbe& rhs) {
          if (lhs.supportUnion != rhs.supportUnion) {
            return lhs.supportUnion < rhs.supportUnion;
          }
          if (lhs.first != rhs.first) {
            return lhs.first < rhs.first;
          }
          if (lhs.second != rhs.second) {
            return lhs.second < rhs.second;
          }
          return lhs.third < rhs.third;
        });

    size_t attemptedTripleProbes = 0;
    for (const auto& probe : tripleProbes) {
      if (attemptedTripleProbes++ >=
          kMaxResetSpecializedExpressionTripleProbes) {
        break;
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
      leafLits,
      /*createMissingLeaves=*/true,
      std::max(
          leafLits.size() * 4 + proofExprs.size(),
          proofExprs.size() * static_cast<size_t>(256)));

  // The expressions were already rewritten through initial assignments and
  // equality classes, so do not add the original equality-pair endpoints back
  // into this local proof. Doing so recreates the sampled AES support blow-up.
  size_t initialEqualityClauses = 0;
  size_t bootstrapEqualityClauses = 0;
  size_t frameInvariantEqualityClauses = 0;
  for (const auto& [lhsExpr, rhsExpr] : *bootstrapEqualityExprs) {
    addLiteralEquivalence(
        solver,
        encoder.encode(lhsExpr),
        encoder.encode(rhsExpr));
    ++bootstrapEqualityClauses;
  }
  for (const auto& [lhsExpr, rhsExpr] : *frameInvariantEqualityExprs) {
    addLiteralEquivalence(
        solver,
        encoder.encode(lhsExpr),
        encoder.encode(rhsExpr));
    ++frameInvariantEqualityClauses;
  }

  for (size_t i = 0; i < cube.size(); ++i) {
    const int lit = encoder.encode(proofExprs[i]);
    const int assumption = cube[i].value ? lit : -lit;
    solver.addClause({assumption});
  }
  const size_t encodedSupportSize = encoder.leafLits().size();
  if (encodedSupportSize > kMaxResetSpecializedExpressionSupport) {
    return miss(
        "encoded_support_cap",
        encodedSupportSize,
        initialEqualityClauses,
        bootstrapEqualityClauses,
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
}

std::optional<StateCube> resetSpecializedConflictCubeAtStep(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    ResetFrontierCache& cache,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant = nullptr,
    bool allowDeepSmallCubeRelaxedBudget = true) {
  StateCube queryCube = cube;
  normalizeCube(queryCube);
  if (problem.resetBootstrapCycles == 0 || queryCube.empty()) {
    return std::nullopt;  // LCOV_EXCL_LINE
  }
  const std::string memoKey =
      resetExpressionConflictCacheKey(queryCube, targetStep, frameInvariant);
  if (const auto* entry =
          lookupResetExpressionConflictMemo(
              cache.resetExpressionConflictByKey, memoKey)) {
    if (!entry->hasConflict) {
      return std::nullopt;
    }
    return entry->conflict;
  }
  const bool deepTargetStep =
      targetStep >
      problem.resetBootstrapCycles +
          kMaxResetSpecializedBadFormulaValidationFrame;
  if (deepTargetStep &&
      resetExpressionBudgetSkipApplies(
          cache.resetExpressionBudgetSkipFromStep,
          queryCube,
          targetStep,
          frameInvariant)) {
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression miss "
          "reason=deep_budget_skip cube=",
          queryCube.size(),
          " target_step=",
          targetStep,
          " support=0 initial_equalities=0 bootstrap_equalities=0 "
          "frame_invariant_equalities=0 literals=",
          formatCubeForDiag(queryCube),
          " hash=",
          cubeFingerprint(queryCube));
    }
    rememberResetExpressionConflictMemo(
        cache.resetExpressionConflictByKey, memoKey, std::nullopt);
    return std::nullopt;
  }
  const auto remember = [&](std::optional<StateCube> conflict)
      -> std::optional<StateCube> {
    if (conflict.has_value()) {
      normalizeCube(*conflict);
    }
    rememberResetExpressionConflictMemo(
        cache.resetExpressionConflictByKey, memoKey, conflict);
    return conflict;
  };

  ResetSymbolicEvaluator& evaluator =
      resetSymbolicEvaluatorFor(cache, problem, transitionByState);
  const bool useDeepSmallCubeBudget =
      allowDeepSmallCubeRelaxedBudget &&
      queryCube.size() <= kMaxDeepSmallCubeResetSymbolicLiterals &&
      deepTargetStep;
  std::optional<ScopedResetSymbolicEvaluatorBudget> scopedBudget;
  if (useDeepSmallCubeBudget) {
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression relaxed_budget cube=",
          queryCube.size(),
          " target_step=",
          targetStep,
          " state_limit=",
          kMaxDeepSmallCubeResetSymbolicEvaluatorStates,
          " expr_limit=",
          kMaxDeepSmallCubeResetSymbolicEvaluatorExprs,
          " hash=",
          cubeFingerprint(queryCube));
    }
    scopedBudget.emplace(
        evaluator,
        kMaxDeepSmallCubeResetSymbolicEvaluatorStates,
        kMaxDeepSmallCubeResetSymbolicEvaluatorExprs);
  }
  std::vector<BoolExpr*> resetExprs;
  resetExprs.reserve(queryCube.size());
  for (const auto& literal : queryCube) {
    const auto expr = evaluator.stateExpr(literal.symbol, targetStep);
    if (!expr.has_value()) {
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
    resetExprs.push_back(*expr);
    if (isConstExpr(*expr, !literal.value)) {
      return remember(StateCube{literal});
    }
  }
  if (evaluator.budgetExhausted()) {
    return remember(
        resetSpecializedExpressionConflictCube(
            problem,
            transitionByState,
            evaluator,
            queryCube,
            targetStep,
            frameInvariant,
            &cache.resetExpressionConflictByKey,
            &cache.resetExpressionBudgetSkipFromStep));  // LCOV_EXCL_LINE
  }

  if (const auto conflict =
          findResetExpressionRelationConflict(resetExprs, queryCube);
      conflict.has_value()) {
    return remember(*conflict);
  }

  auto& canonicalizer = resetExpressionCanonicalizerFor(cache, problem);
  if (canonicalizer.inconsistent()) {
    StateCube conflict = queryCube;
    normalizeCube(conflict);
    return remember(conflict);  // LCOV_EXCL_LINE
  }
  std::vector<BoolExpr*> canonicalExprs;
  canonicalExprs.reserve(resetExprs.size());
  size_t canonicalizeBudget = kMaxDeepResetExpressionCanonicalizeNodes;
  for (size_t i = 0; i < resetExprs.size(); ++i) {
    BoolExpr* canonical = nullptr;
    if (useDeepSmallCubeBudget) {
      auto bounded =
          canonicalizer.canonicalizeBounded(resetExprs[i], canonicalizeBudget);
      if (!bounded.has_value()) {
        rememberResetExpressionBudgetSkip(
            cache.resetExpressionBudgetSkipFromStep,
            queryCube,
            targetStep,
            frameInvariant);
        if (pdrResetShortcutDiagEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression miss "
              "reason=canonicalize_budget cube=",
              queryCube.size(),
              " target_step=",
              targetStep,
              " support=0 initial_equalities=0 bootstrap_equalities=0 "
              "frame_invariant_equalities=0 literals=",
              formatCubeForDiag(queryCube),
              " hash=",
              cubeFingerprint(queryCube));
        }
        return remember(std::nullopt);
      }
      canonical = *bounded;
    } else {
      canonical = canonicalizer.canonicalize(resetExprs[i]);
    }
    canonicalExprs.push_back(canonical);
    if (isConstExpr(canonical, !queryCube[i].value)) {
      return remember(StateCube{queryCube[i]});
    }
  }
  if (const auto conflict =
          findResetExpressionRelationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression conflict cube=",
          queryCube.size(),
          "->",
          conflict->size(),
          " via=canonical hash=",
          cubeFingerprint(*conflict));
    }
    return remember(*conflict);
  }
  if (const auto conflict =
          findResetExpressionImplicationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression conflict cube=",
          queryCube.size(),
          "->",
          conflict->size(),
          " via=implication hash=",
          cubeFingerprint(*conflict));
    }
    return remember(*conflict);
  }
  if (const auto conflict =
          findAffineXorRelationConflict(canonicalExprs, queryCube);
      conflict.has_value()) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized expression conflict cube=",
          queryCube.size(),
          "->",
          conflict->size(),
          " via=affine_xor hash=",
          cubeFingerprint(*conflict));
    }
    return remember(*conflict);
  }

  auto* bootstrapRelations = resetBootstrapExpressionRelationsFor(
      cache, problem, transitionByState, evaluator, canonicalizer);
  if (bootstrapRelations == nullptr) {
    return resetSpecializedExpressionConflictCube(
        problem,
        transitionByState,
        evaluator,
        queryCube,
        targetStep,
        frameInvariant,
        &cache.resetExpressionConflictByKey,
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
            " via=bootstrap_relation hash=",
            cubeFingerprint(*conflict));
      }
      return remember(*conflict);
    }

    // Direct bootstrap equality detects only whole-expression matches.  For
    // local equality sets, quotient candidate expressions through bootstrap
    // relations before opening the optional SAT proof.  Large ASIC equality
    // sets skip this optional rewrite and keep the already-sound index/SAT
    // fallback, because sampling showed the rewrite itself becoming the wall.
    if (bootstrapRelations->hasRewriter &&
        bootstrapRelations->rewriter.inconsistent()) {
      StateCube conflict = queryCube;
      normalizeCube(conflict);
      return remember(conflict);  // LCOV_EXCL_LINE
    }
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
          return remember(StateCube{queryCube[i]});
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
              findResetExpressionImplicationConflict(rewrittenExprs, queryCube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              queryCube.size(),
              "->",
              conflict->size(),
              " via=bootstrap_rewrite_implication hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
      if (const auto conflict =
              findAffineXorRelationConflict(rewrittenExprs, queryCube);
          conflict.has_value()) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: reset-specialized expression conflict cube=",
              queryCube.size(),
              "->",
              conflict->size(),
              " via=bootstrap_rewrite_affine_xor hash=",
              cubeFingerprint(*conflict));
        }
        return remember(*conflict);
      }
    }
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

void addFormulaSymbols(BoolExpr* formula, std::unordered_set<size_t>& symbols) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
}

void addFormulaStateSupport(BoolExpr* formula,
                            const std::unordered_set<size_t>& stateSymbols,
                            std::unordered_set<size_t>& output) {
  if (formula == nullptr) {
    return;  // LCOV_EXCL_LINE
  }
  for (const auto symbol : formula->getSupportVars()) {
    if (stateSymbols.find(symbol) != stateSymbols.end()) {
      output.insert(symbol);
    }
  }
}

void addRelevantComplementedStatePartners(
    const ComplementPartnerIndex& complementPartners,
    std::unordered_set<size_t>& symbols) {
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
  for (size_t cursor = 0; cursor < worklist.size(); ++cursor) {
    const auto partnerIt =
        complementPartners.partnersBySymbol.find(worklist[cursor]);
    if (partnerIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    for (const auto partnerSymbol : partnerIt->second) {
      if (symbols.insert(partnerSymbol).second) {
        worklist.push_back(partnerSymbol);
      }
    }
  }
}

void addRelevantComplementedStatePartners(
    const std::vector<std::pair<size_t, size_t>>& complementedStatePairs,
    std::unordered_set<size_t>& symbols) {
  for (const auto& [primarySymbol, complementedSymbol] : complementedStatePairs) {
    if (symbols.find(primarySymbol) != symbols.end() ||
        symbols.find(complementedSymbol) != symbols.end()) {
      symbols.insert(primarySymbol);
      symbols.insert(complementedSymbol);
    }
  }
}

bool hasStructuredInitFacts(const KInductionProblem& problem) {
  if (problem.resetBootstrapCycles != 0) {
    return !problem.bootstrapStateAssignments.empty() ||
           !problem.bootstrapStateEqualityPairs.empty();
  }
  return !problem.initialStateAssignments.empty() ||
         !problem.initialStateEqualityPairs.empty();
}

void addRelevantInitConstraintSymbols(const KInductionProblem& problem,
                                      std::unordered_set<size_t>& symbols) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  for (const auto& [symbol, /*value*/ _] : assignments) {
    if (symbols.find(symbol) != symbols.end()) {
      symbols.insert(symbol);
    }
  }
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
  std::vector<size_t> worklist(symbols.begin(), symbols.end());
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
    for (const auto clauseIndex : indexIt->second) {
      if (includedClauses >= maxProjectedFrameClauses ||
          includedLiterals >= maxProjectedFrameLiterals) {
        return;
      }
      if (frame.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
        continue;
      }
      const auto& clause = frame.clauses[clauseIndex];
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;
      }
      if (includedLiterals + clause.size() > maxProjectedFrameLiterals &&
          includedClauses != 0) {
        continue;
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
                               std::unordered_set<size_t>& symbols) {
  if (level == 0) {
    if (hasStructuredInitFacts(problem)) {
      // Keep Init cone-local even in the exact frame-clause retry. ASIC SEC
      // startup frontiers contain tens of thousands of equality facts, while a
      // predecessor query usually touches only a few of them. The exact retry
      // below disables learned-frame filtering, not this structured Init
      // sparsification.
      addRelevantInitConstraintSymbols(problem, symbols);
    } else {
      addFormulaSymbols(initFormula, symbols);
    }
    if (problem.resetBootstrapCycles != 0 && problem.property != nullptr) {
      // PDREngine::run validates the concrete reset/bootstrap F[0] frontier
      // before any PDR query can use it.  The checked safety property is then
      // a real F[0] fact, even when structured init encoding is used instead
      // of the monolithic initFormula.
      addFormulaSymbols(problem.property, symbols);
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
    addFormulaSymbols(frameInvariant, symbols);
    if (exactFrameClauses) {
      addAllFrameClauseSymbols(frames[level], symbols);
    } else {
      addRelevantFrameClauseSymbols(problem, frames[level], symbols);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
}

void addEncodedTransitionTargetSymbols(
    const KInductionProblem& problem,
    const ComplementPartnerIndex& complementPartners,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& transitionSupportSymbols,
    std::unordered_set<size_t>& symbols) {
  // The predecessor query asks for one concrete transition into a target cube.
  // Its target list and support set are computed once in findPredecessorCube()
  // and threaded through these helpers; recomputing support here is expensive
  // on ASIC cones because each resolver lookup can walk a large formula DAG.
  symbols.insert(encodedTargets.begin(), encodedTargets.end());
  symbols.insert(transitionSupportSymbols.begin(), transitionSupportSymbols.end());
  addRelevantComplementedStatePartners(complementPartners, symbols);
}

std::vector<size_t> findBadQuerySymbols(const KInductionProblem& problem,
                                        BoolExpr* initFormula,
                                        BoolExpr* frameInvariant,
                                        const std::vector<FrameClauses>& frames,
                                        BoolExpr* badFormula,
                                        size_t level,
                                        const ComplementPartnerIndex& complementPartners,
                                        bool exactFrameClauses) {
  std::unordered_set<size_t> symbols;
  addFormulaSymbols(badFormula, symbols);
  addFrameConstraintSymbols(
      problem,
      initFormula,
      frameInvariant,
      frames,
      level,
      exactFrameClauses,
      complementPartners,
      symbols);
  return sortUniqueSymbols(std::move(symbols));
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
    const std::vector<StateClause>* extraFrameClauses) {
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
      symbols);
  if (predecessorSourceFrameIsKnownSafe(level)) {
    // The safe-frame property is encoded below, but it must not widen the
    // projected learned-frame surface. Otherwise every property-support state
    // bit can pull in large neighborhoods of unrelated frame clauses.
    addFormulaSymbols(problem.property, symbols);
  }
  for (const auto symbol : transitionSupportSymbols) {
    if (symbol >= 2) {
      symbols.insert(symbol);
    }
  }
  addRelevantComplementedStatePartners(complementPartners, symbols);
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
  return sortUniqueSymbols(std::move(symbols));
}

std::optional<bool> findCubeLiteralValue(const StateCube& cube, size_t symbol) {
  const auto it = std::lower_bound(
      cube.begin(),
      cube.end(),
      symbol,
      [](const CubeLiteral& literal, size_t requestedSymbol) {
        return literal.symbol < requestedSymbol;
      });
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
      return true;
    }
  }
  return false;
}

bool contradictsEqualities(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& equalities) {
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsValue = findCubeLiteralValue(cube, lhsSymbol);
    const auto rhsValue = findCubeLiteralValue(cube, rhsSymbol);
    if (lhsValue.has_value() && rhsValue.has_value() &&
        *lhsValue != *rhsValue) {
      return true;
    }
  }
  return false;
}

bool contradictsComplements(
    const StateCube& cube,
    const std::vector<std::pair<size_t, size_t>>& complements) {
  for (const auto& [primarySymbol, complementedSymbol] : complements) {
    const auto primaryValue = findCubeLiteralValue(cube, primarySymbol);
    const auto complementedValue = findCubeLiteralValue(cube, complementedSymbol);
    if (primaryValue.has_value() && complementedValue.has_value() &&
        *primaryValue == *complementedValue) {
      return true;
    }
  }
  return false;
}

std::optional<bool> cubeIntersectsKnownInitFacts(
    const KInductionProblem& problem,
    const StateCube& cube) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  if (contradictsAssignments(cube, assignments) ||
      contradictsEqualities(cube, equalities)) {
    return false;
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs0)) {
    return false;
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck &&
      contradictsComplements(cube, problem.complementedStatePairs1)) {
    return false;
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
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    bool createMissingTransitionLeaves = false,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  for (const auto& group :
       groupTransitionTargetsBySymbolMap(transitionByState, encodedTargets)) {
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(frame, supportSymbols),
        group.symbolMap,
        createMissingTransitionLeaves,
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols));
    for (const auto stateSymbol : group.stateSymbols) {
      try {
        const TransitionExprView view =
            transitionByState.expressionView(stateSymbol);
        if (view.symbolMap != group.symbolMap) {
          throw std::runtime_error("Inconsistent transition symbol map");
        }
        addLiteralEquivalence(
            solver,
            variables.getLiteral(stateSymbol, frame + 1),
            encoder.encode(view.expr));
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR transition relation encoding failed for target state symbol " +
            std::to_string(stateSymbol) + " at frame " + std::to_string(frame) +
            " with " + std::to_string(supportSymbols.size()) +
            " support symbols: " + error.what());
      }
    }
    if (encodedLeafLits != nullptr) {
      const auto& groupLeafLits = encoder.leafLits();
      encodedLeafLits->insert(groupLeafLits.begin(), groupLeafLits.end());
    }
  }
}

void addTransitionConstraintsForTargetCube(
    SATSolverWrapper& solver,
    const FrameVariableStore& variables,
    const TransitionExprResolver& transitionByState,
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols,
    std::unordered_map<size_t, int>* encodedLeafLits = nullptr) {
  (void)encodedTargets;
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(frame, supportSymbols),
        group.symbolMap,
        false,
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols));
    for (const auto& literal : group.literals) {
      int transitionLit = 0;
      try {
        const TransitionExprView view =
            transitionByState.expressionView(literal.transitionSymbol);
        if (view.symbolMap != group.symbolMap) {
          throw std::runtime_error("Inconsistent transition symbol map");
        }
        transitionLit = encoder.encode(view.expr);
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR predecessor transition encoding failed for target state symbol " +
            std::to_string(literal.transitionSymbol) + " at frame " +
            std::to_string(frame) + " with " +
            std::to_string(supportSymbols.size()) + " support symbols: " +
            error.what());
      }
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
    size_t frame,
    const StateCube& targetCube,
    const std::vector<size_t>& encodedTargets,
    const std::vector<size_t>& supportSymbols) {
  (void)encodedTargets;
  std::vector<std::pair<int, CubeLiteral>> assumptions;
  assumptions.reserve(targetCube.size());
  for (const auto& group :
       groupTransitionCubeLiteralsBySymbolMap(transitionByState, targetCube)) {
    FrameFormulaEncoder encoder(
        solver,
        variables.makeLeafLits(frame, supportSymbols),
        group.symbolMap,
        false,
        estimateTransitionEncodingNodes(transitionByState, group.stateSymbols));
    for (const auto& literal : group.literals) {
      int transitionLit = 0;
      try {
        const TransitionExprView view =
            transitionByState.expressionView(literal.transitionSymbol);
        if (view.symbolMap != group.symbolMap) {
          throw std::runtime_error("Inconsistent transition symbol map");
        }
        transitionLit = encoder.encode(view.expr);
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR predecessor core encoding failed for target state symbol " +
            std::to_string(literal.transitionSymbol) + " at frame " +
            std::to_string(frame) + " with " +
            std::to_string(supportSymbols.size()) +
            " support symbols: " + error.what());
      }
      assumptions.emplace_back(
          literal.desiredValue ? transitionLit : -transitionLit,
          literal.originalLiteral);
    }
  }
  return assumptions;
}

std::optional<StateCube> findPreviousResetCoreImpliedByOneStepTransition(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& targetCube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache) {
  if (postBootstrapSteps == 0) {
    return std::nullopt;
  }
  const auto previousIt =
      cache.resetUnreachableCoresByPostBootstrapStep.find(
          postBootstrapSteps - 1);
  if (previousIt ==
          cache.resetUnreachableCoresByPostBootstrapStep.end() ||
      previousIt->second.empty()) {
    return std::nullopt;
  }

  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  if (encodedTargets.empty()) {
    return std::nullopt;
  }
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
  if (transitionSupportSymbols.size() >
      kMaxPreviousResetCoreImplicationSupport) {
    if (pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: previous reset blocker implication skipped "
          "reason=support_cap post_bootstrap_steps=",
          postBootstrapSteps,
          " support=",
          transitionSupportSymbols.size(),
          " target_cube=",
          targetCube.size());
    }
    return std::nullopt;
  }

  size_t checks = 0;
  for (const StateCube& previousCore : previousIt->second) {
    if (previousCore.empty() ||
        previousCore.size() >
            kMaxPreviousResetCoreImplicationCoreLiterals) {
      continue;
    }
    if (++checks > kMaxPreviousResetCoreImplicationChecks) {
      break;
    }

    std::unordered_set<size_t> querySymbols(
        transitionSupportSymbols.begin(), transitionSupportSymbols.end());
    for (const auto& literal : previousCore) {
      querySymbols.insert(literal.symbol);
    }
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs0, querySymbols);
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs1, querySymbols);
    const std::vector<size_t> solverSymbols =
        sortUniqueSymbols(std::move(querySymbols));
    if (solverSymbols.size() >
        kMaxPreviousResetCoreImplicationSupport) {
      continue;
    }

    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(solverSymbols.size());
    FrameVariableStore variables(solver, solverSymbols, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs0, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs1, 1);
    addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
    addTransitionConstraintsForTargetCube(
        solver,
        variables,
        transitionByState,
        0,
        targetCube,
        encodedTargets,
        transitionSupportSymbols);
    addNegatedCubeClause(solver, variables, previousCore, 0);

    SATSolverWrapper::SolveStatus status = SATSolverWrapper::SolveStatus::Sat;
    if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      status = solver.solveWithKissatResourceLimits(
          kPreviousResetCoreImplicationConflictLimit);
    } else {
      status = solver.solveStatus();
    }
    if (status == SATSolverWrapper::SolveStatus::Unsat) {
      if (pdrStatsEnabled() || pdrResetShortcutDiagEnabled()) {
        emitSecDiag(
            "SEC PDR stats: previous reset blocker implication ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " target_cube=",
            targetCube.size(),
            " previous_core=",
            previousCore.size(),
            " support=",
            transitionSupportSymbols.size(),
            " solver_symbols=",
            solverSymbols.size());
      }
      return previousCore;
    }
    if (status == SATSolverWrapper::SolveStatus::Unknown &&
        pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: previous reset blocker implication skipped "
          "reason=solver_resource_limit post_bootstrap_steps=",
          postBootstrapSteps,
          " target_cube=",
          targetCube.size(),
          " previous_core=",
          previousCore.size(),
          " solver_symbols=",
          solverSymbols.size());
    }
  }
  return std::nullopt;
}

std::optional<StateCube> proveTransitionImpossibleResetCoreForCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    ResetFrontierCache& cache) {
  if (problem.resetBootstrapCycles == 0) {
    return std::nullopt;
  }
  if (const auto cachedCore =
          findTransitionImpossibleResetCoreForCube(cache, cube);
      cachedCore.has_value()) {
    return cachedCore;
  }

  std::vector<StateCube> candidates;
  std::unordered_set<std::string> candidateKeys;
  for (const auto& [_, cores] : cache.resetUnreachableCoresByPostBootstrapStep) {
    (void)_;
    for (const StateCube& core : cores) {
      if (core.empty() ||
          core.size() > kMaxTransitionImpossibleResetCoreLiterals ||
          !cubeContainsCube(cube, core)) {
        continue;
      }
      const std::string key = resetFrontierCacheKey(core, 0);
      const auto memoIt = cache.transitionImpossibleResetCoreByKey.find(key);
      if (memoIt != cache.transitionImpossibleResetCoreByKey.end()) {
        if (memoIt->second) {
          return core;
        }
        continue;
      }
      if (candidateKeys.insert(key).second) {
        candidates.push_back(core);
      }
    }
  }
  if (candidates.empty()) {
    return std::nullopt;
  }

  std::sort(
      candidates.begin(),
      candidates.end(),
      [](const StateCube& lhs, const StateCube& rhs) {
        if (lhs.size() != rhs.size()) {
          return lhs.size() < rhs.size();
        }
        return cubeFingerprint(lhs) < cubeFingerprint(rhs);
      });

  for (const StateCube& candidate : candidates) {
    const std::string key = resetFrontierCacheKey(candidate, 0);
    const std::vector<size_t> targetSymbols = cubeStateSymbols(candidate);
    const std::vector<size_t> encodedTargets =
        expandTransitionTargets(problem, targetSymbols, transitionByState);
    if (encodedTargets.empty()) {
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);
      continue;
    }
    const std::vector<size_t> transitionSupportSymbols =
        collectTransitionSupportSymbols(transitionByState, encodedTargets);
    if (transitionSupportSymbols.size() >
        kMaxTransitionImpossibleResetCoreSupport) {
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);
      if (pdrResetShortcutDiagEnabled()) {
        emitSecDiag(
            "SEC PDR stats: transition-impossible reset core skipped "
            "reason=support_cap core=",
            candidate.size(),
            " support=",
            transitionSupportSymbols.size());
      }
      continue;
    }

    std::unordered_set<size_t> querySymbols(
        transitionSupportSymbols.begin(), transitionSupportSymbols.end());
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs0, querySymbols);
    addRelevantComplementedStatePartners(
        problem.complementedStatePairs1, querySymbols);
    const std::vector<size_t> solverSymbols =
        sortUniqueSymbols(std::move(querySymbols));
    if (solverSymbols.size() > kMaxTransitionImpossibleResetCoreSupport) {
      cache.transitionImpossibleResetCoreByKey.emplace(key, false);
      continue;
    }

    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(solverSymbols.size());
    FrameVariableStore variables(solver, solverSymbols, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs0, 1);
    addComplementedStateRelations(
        solver, variables, problem.complementedStatePairs1, 1);
    addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
    addTransitionConstraintsForTargetCube(
        solver,
        variables,
        transitionByState,
        0,
        candidate,
        encodedTargets,
        transitionSupportSymbols);

    SATSolverWrapper::SolveStatus status = SATSolverWrapper::SolveStatus::Sat;
    if (solverType == KEPLER_FORMAL::Config::SolverType::KISSAT) {
      status = solver.solveWithKissatResourceLimits(
          kTransitionImpossibleResetCoreConflictLimit);
    } else {
      status = solver.solveStatus();
    }
    if (status == SATSolverWrapper::SolveStatus::Unsat) {
      rememberTransitionImpossibleResetCore(cache, candidate);
      if (pdrStatsEnabled() || pdrResetShortcutDiagEnabled()) {
        emitSecDiag(
            "SEC PDR stats: transition-impossible reset core ",
            "cube=", cube.size(),
            " core=", candidate.size(),
            " support=", transitionSupportSymbols.size(),
            " solver_symbols=", solverSymbols.size(),
            " hash=", cubeFingerprint(candidate));
      }
      return candidate;
    }
    cache.transitionImpossibleResetCoreByKey.emplace(key, false);
    if (status == SATSolverWrapper::SolveStatus::Unknown &&
        pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: transition-impossible reset core skipped "
          "reason=solver_resource_limit core=",
          candidate.size(),
          " solver_symbols=",
          solverSymbols.size());
    }
  }
  return std::nullopt;
}

std::optional<StateCube> resetSpecializedPriorCoreConflictAtStep(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    size_t targetStep,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant,
    bool allowDeepSmallCubeRelaxedBudget = true) {
  if (postBootstrapSteps == 0) {
    return std::nullopt;
  }

  std::vector<StateCube> candidates;
  std::unordered_set<std::string> candidateKeys;
  for (const auto& [knownStep, cores] :
       cache.resetUnreachableCoresByPostBootstrapStep) {
    if (knownStep >= postBootstrapSteps) {
      continue;
    }
    for (const StateCube& core : cores) {
      if (core.empty() || core.size() >= cube.size() ||
          !cubeContainsCube(cube, core)) {
        continue;
      }
      if (candidateKeys.insert(resetFrontierCacheKey(core, 0)).second) {
        candidates.push_back(core);
      }
    }
  }
  if (candidates.empty()) {
    return std::nullopt;
  }

  std::sort(
      candidates.begin(),
      candidates.end(),
      [](const StateCube& lhs, const StateCube& rhs) {
        if (lhs.size() != rhs.size()) {
          return lhs.size() < rhs.size();
        }
        return cubeFingerprint(lhs) < cubeFingerprint(rhs);
      });

  size_t probes = 0;
  for (const StateCube& candidate : candidates) {
    if (probes++ >= kMaxPriorResetCoreSpecializedProbes) {
      break;
    }

    // A core proved unreachable at an earlier reset step is only a candidate
    // here.  Re-prove it at the current target step before using it; this keeps
    // the shortcut an exact reset-image proof while avoiding the measured huge
    // full-cube frontier SAT query.
    if (const auto conflict =
            resetSpecializedConflictCubeAtStep(
                problem,
                transitionByState,
                cache,
                candidate,
                targetStep,
                frameInvariant,
                allowDeepSmallCubeRelaxedBudget);
        conflict.has_value() && cubeContainsCube(cube, *conflict)) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: prior reset core specialized conflict ",
            "post_bootstrap_steps=", postBootstrapSteps,
            " cube=", cube.size(),
            " candidate=", candidate.size(),
            "->", conflict->size(),
            " probes=", probes,
            " hash=", cubeFingerprint(*conflict));
      }
      return *conflict;
    }
  }
  return std::nullopt;
}

std::optional<StateCube> memoizedResetSpecializedConflictCubeAtStep(
    const ResetFrontierCache& cache,
    const StateCube& cube,
    size_t targetStep,
    BoolExpr* frameInvariant) {
  StateCube queryCube = cube;
  normalizeCube(queryCube);
  const std::string memoKey =
      resetExpressionConflictCacheKey(queryCube, targetStep, frameInvariant);
  const auto* entry =
      lookupResetExpressionConflictMemo(
          cache.resetExpressionConflictByKey, memoKey);
  if (entry == nullptr || !entry->hasConflict) {
    return std::nullopt;
  }
  return entry->conflict;
}

std::optional<StateCube> memoizedPriorResetCoreConflictAtStep(
    const StateCube& cube,
    size_t postBootstrapSteps,
    size_t targetStep,
    const ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (postBootstrapSteps == 0) {
    return std::nullopt;
  }

  for (const auto& [knownStep, cores] :
       cache.resetUnreachableCoresByPostBootstrapStep) {
    if (knownStep >= postBootstrapSteps) {
      continue;
    }
    for (const StateCube& core : cores) {
      if (core.empty() || core.size() >= cube.size() ||
          !cubeContainsCube(cube, core)) {
        continue;
      }
      if (const auto conflict =
              memoizedResetSpecializedConflictCubeAtStep(
                  cache, core, targetStep, frameInvariant);
          conflict.has_value() && cubeContainsCube(cube, *conflict)) {
        return *conflict;
      }
    }
  }
  return std::nullopt;
}

std::vector<size_t> predecessorProjectionSymbols(
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* initFormula,
    BoolExpr* frameInvariant,
    const std::vector<FrameClauses>& frames,
    size_t level,
    const ComplementPartnerIndex& complementPartners,
    const std::vector<size_t>& transitionSupportSymbols) {
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
      addFormulaStateSupport(initFormula, stateSymbolSet, projection);
    }
  } else {
    addRelevantFrameClauseSymbols(problem, frames[level], projection);
    addFormulaStateSupport(frameInvariant, stateSymbolSet, projection);
  }
  addRelevantComplementedStatePartners(complementPartners, projection);
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

void addTransitionRelation(SATSolverWrapper& solver,
                           const FrameVariableStore& variables,
                           const KInductionProblem& problem,
                           size_t frame) {
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
  for (const auto& [stateSymbol, expr] : problem.transitions0) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
  for (const auto& [stateSymbol, expr] : problem.transitions1) {
    addLiteralEquivalence(
        solver,
        variables.getLiteral(stateSymbol, frame + 1),
        encoder.encode(expr));
  }
}

void normalizeCube(StateCube& cube) {
  // Canonical ordering lets us compare cubes structurally and avoid learning
  // the same obligation more than once with a different literal order.
  std::sort(cube.begin(), cube.end(), [](const CubeLiteral& lhs, const CubeLiteral& rhs) {
    if (lhs.symbol != rhs.symbol) {
      return lhs.symbol < rhs.symbol;
    }
    return lhs.value < rhs.value;  // LCOV_EXCL_LINE
  });
  cube.erase(std::unique(cube.begin(), cube.end()), cube.end());
}

void normalizeClause(StateClause& clause) {
  // Clauses are canonicalized for the same reason: later subsumption and
  // convergence checks depend on stable ordering and deduplication.
  std::sort(
      clause.begin(), clause.end(), [](const ClauseLiteral& lhs, const ClauseLiteral& rhs) {
        if (lhs.symbol != rhs.symbol) {
          return lhs.symbol < rhs.symbol;
        }
        return lhs.positive < rhs.positive;  // LCOV_EXCL_LINE
      });
  clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
}

SymbolPair canonicalPair(size_t lhs, size_t rhs) {
  if (rhs < lhs) {
    std::swap(lhs, rhs);
  }
  return SymbolPair{lhs, rhs};
}

InitFactIndex buildInitFactIndex(const KInductionProblem& problem) {
  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

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
  index.complements.reserve(
      problem.complementedStatePairs0.size() +
      problem.complementedStatePairs1.size());
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs0) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  for (const auto& [primarySymbol, complementedSymbol] :
       problem.complementedStatePairs1) {
    index.complements.insert(canonicalPair(primarySymbol, complementedSymbol));
    index.relations.addComplement(primarySymbol, complementedSymbol);
  }
  index.rootAssignments.reserve(index.assignments.size());
  for (const auto& [symbol, value] : index.assignments) {
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
  // 100+ literal cube makes the engine enumerate many adjacent impossible
  // startup states.  This extractor turns the visible conflict into the
  // smallest safe cube:
  //   - one literal for an init assignment conflict;
  //   - two literals for equality/complement conflicts.
  // The learned clause is still exactly an Init consequence, but much stronger.
  std::unordered_map<size_t, std::pair<bool, CubeLiteral>> cubeValueByRoot;
  cubeValueByRoot.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto root = facts.relations.findWithParity(literal.symbol);
    if (!root.has_value()) {
      const auto assignment = facts.assignments.find(literal.symbol);
      if (assignment == facts.assignments.end() ||
          assignment->second == literal.value) {
        continue;
      }
      StateCube conflict{literal};
      normalizeCube(conflict);
      return conflict;
    }

    const bool rootValue = literal.value ^ root->second;
    const auto assignment = facts.rootAssignments.find(root->first);
    if (assignment != facts.rootAssignments.end() &&
        assignment->second != rootValue) {
      StateCube conflict{literal};
      normalizeCube(conflict);
      return conflict;
    }

    if (const auto it = cubeValueByRoot.find(root->first);
        it != cubeValueByRoot.end()) {
      if (it->second.first != rootValue) {
        StateCube conflict{it->second.second, literal};
        normalizeCube(conflict);
        return conflict;
      }
      continue;
    }
    cubeValueByRoot.emplace(root->first, std::pair{rootValue, literal});
  }

  return std::nullopt;
}

bool twoLiteralCubeIsKnownOutsideInit(const InitFactIndex& facts,
                                      size_t lhsSymbol,
                                      bool lhsValue,
                                      size_t rhsSymbol,
                                      bool rhsValue) {
  if (const auto lhsAssignment = facts.assignments.find(lhsSymbol);
      lhsAssignment != facts.assignments.end() &&
      lhsAssignment->second != lhsValue) {
    return true;
  }
  if (const auto rhsAssignment = facts.assignments.find(rhsSymbol);
      rhsAssignment != facts.assignments.end() &&
      rhsAssignment->second != rhsValue) {
    return true;
  }
  const auto lhsRoot = facts.relations.findWithParity(lhsSymbol);
  const auto rhsRoot = facts.relations.findWithParity(rhsSymbol);
  if (!lhsRoot.has_value() || !rhsRoot.has_value() ||
      lhsRoot->first != rhsRoot->first) {
    return false;
  }
  return (lhsValue ^ lhsRoot->second) != (rhsValue ^ rhsRoot->second);
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
  frame.clauses.push_back(std::move(clause));
  frame.clauseIndexDirty = true;
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
}

std::optional<std::vector<StateClause>> stateOnlyBadFormulaClauses(
    BoolExpr* badFormula,
    const std::unordered_set<size_t>& stateSymbols) {
  if (badFormula == nullptr) {
    return std::nullopt;
  }

  const auto supportSet = badFormula->getSupportVars();
  if (supportSet.size() > kMaxValidatedBadFormulaCnfSupport) {
    return std::nullopt;
  }
  for (const auto symbol : supportSet) {
    if (stateSymbols.find(symbol) == stateSymbols.end()) {
      return std::nullopt;
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
    clauses.push_back(std::move(clause));
  }
  return clauses;
}

bool appendStateOnlyBadFormulaClauses(
    std::vector<StateClause>& target,
    BoolExpr* badFormula,
    const std::unordered_set<size_t>& stateSymbols) {
  const auto clauses = stateOnlyBadFormulaClauses(badFormula, stateSymbols);
  if (!clauses.has_value() || clauses->empty()) {
    return false;
  }
  if (target.size() + clauses->size() > kMaxValidatedBadFormulaClauses) {
    return false;
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
  size_t totalClauses = 0;
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
    appendStateOnlyBadFormulaClauses(clauses, outputBad, stateSymbols);
    if (!clauses.empty()) {
      totalClauses += clauses.size();
      groups.push_back(ObservedOutputBadClauseGroup{
          output, outputBad, std::move(clauses)});
    }
    if (totalClauses >= kMaxValidatedBadFormulaClauses) {
      break;
    }
  }
  return groups;
}

std::optional<std::vector<StateClause>> observedOutputBadFormulaClauses(
    const KInductionProblem& problem,
    const std::unordered_set<size_t>& stateSymbols) {
  const auto groups = observedOutputBadFormulaClauseGroups(problem, stateSymbols);
  if (groups.empty()) {
    return std::nullopt;
  }

  std::vector<StateClause> clauses;
  for (const auto& group : groups) {
    clauses.insert(clauses.end(), group.clauses.begin(), group.clauses.end());
    if (clauses.size() >= kMaxValidatedBadFormulaClauses) {
      break;
    }
  }
  if (clauses.empty()) {
    return std::nullopt;
  }
  return clauses;
}

bool hasNewValidatedBadFormulaClause(
    const std::vector<FrameClauses>& frames,
    const std::vector<StateClause>& clauses,
    size_t targetFrame) {
  for (const auto& clause : clauses) {
    StateClause normalizedClause = clause;
    normalizeClause(normalizedClause);
    for (size_t level = 1; level <= targetFrame && level < frames.size(); ++level) {
      if (!frameHasSubsumingClause(frames[level], normalizedClause)) {
        return true;
      }
    }
  }
  return false;
}

bool hasNewValidatedBadFormulaClauseAtFrame(
    const std::vector<FrameClauses>& frames,
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
  return false;
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

std::string badFormulaValidationCacheKey(
    const std::vector<StateClause>& clauses,
    size_t targetFrame) {
  std::string key;
  key.reserve(32 + clauses.size() * 24);
  key.append(std::to_string(targetFrame));
  for (const auto& clause : clauses) {
    key.push_back('|');
    for (const auto& literal : clause) {
      key.append(std::to_string(literal.symbol));
      key.push_back(literal.positive ? '+' : '-');
      key.push_back(',');
    }
  }
  return key;
}

size_t countCachedResetValidatedBadFormulaAssignments(
    const std::vector<StateClause>& clauses,
    size_t targetFrame,
    const ResetFrontierCache& resetFrontierCache) {
  size_t count = 0;
  for (const auto& clause : clauses) {
    if (findPdrResetUnreachableCoreForCube(
            resetFrontierCache,
            cubeForbiddenByStateClause(clause),
            targetFrame)
        .has_value()) {
      ++count;
    }
  }
  return count;
}

bool frameInvariantImpliesClauses(
    BoolExpr* frameInvariant,
    KEPLER_FORMAL::Config::SolverType solverType,
    const std::vector<StateClause>& clauses) {
  if (frameInvariant == nullptr || clauses.empty()) {
    return false;
  }

  const auto invariantSupport = frameInvariant->getSupportVars();
  for (const auto& clause : clauses) {
    std::unordered_set<size_t> querySymbols(
        invariantSupport.begin(), invariantSupport.end());
    const StateCube forbiddenCube = cubeForbiddenByStateClause(clause);
    for (const auto& literal : forbiddenCube) {
      querySymbols.insert(literal.symbol);
    }

    const std::vector<size_t> solverSymbols =
        sortUniqueSymbols(std::move(querySymbols));
    SATSolverWrapper solver(solverType);
    solver.configureForSecPdrQuery(solverSymbols.size());
    FrameVariableStore variables(solver, solverSymbols, 1);
    FrameFormulaEncoder encoder(
        solver, variables.makeLeafLits(0, invariantSupport));
    solver.addClause({encoder.encode(frameInvariant)});
    for (const auto& literal : forbiddenCube) {
      const int satLiteral = variables.getLiteral(literal.symbol, 0);
      solver.addClause({literal.value ? satLiteral : -satLiteral});
    }
    if (solver.solve()) {
      return false;
    }
  }
  return true;
}

std::vector<std::vector<std::pair<size_t, bool>>> forbiddenAssignmentCubes(
    const std::vector<StateClause>& clauses) {
  std::vector<std::vector<std::pair<size_t, bool>>> cubes;
  cubes.reserve(clauses.size());
  for (const auto& clause : clauses) {
    cubes.push_back(cubeAssignments(cubeForbiddenByStateClause(clause)));
  }
  return cubes;
}

std::optional<bool> validateBadFormulaClausesWithResetCubes(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
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
      validationSupportCubeForStateClauses(clauses);
  const bool deepLocalResetSpecializedRepair =
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&
      targetFrame <=
          kMaxFreshDeepResetSpecializedBadFormulaRepairFrame &&
      !allowExactResetFrontierQueries &&
      clauses.size() <=
          kMaxDeepLocalExactResetCubeValidatedBadFormulaClauses &&
      !validationSupportCube.empty() &&
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport;
  const bool deepResetSpecializedOnlyRepair =
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&
      !allowExactResetFrontierQueries &&
      !deepLocalResetSpecializedRepair;
  const bool deepLocalExactResetValidation =
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&
      allowExactResetFrontierQueries &&
      clauses.size() <=
          kMaxDeepLocalExactResetCubeValidatedBadFormulaClauses &&
      !validationSupportCube.empty() &&
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport;
  if (targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&
      clauses.size() > kMaxExactResetCubeValidatedBadFormulaClauses &&
      !deepResetSpecializedOnlyRepair &&
      !deepLocalExactResetValidation &&
      !deepLocalResetSpecializedRepair) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: skipped deep reset-specialized bad-formula "
          "validation ",
          "bad_frame=", targetFrame,
          " clauses=", clauses.size(),
          " support=", validationSupportCube.size());
    }
    return std::nullopt;
  }

  if (allowExactResetFrontierQueries &&
      !validationSupportCube.empty() &&
      validationSupportCube.size() <= kMaxResetCubeValidationPrimeSupport) {
    auto& reachabilityContext = resetReachabilityContextFor(
        resetFrontierCache, problem, transitionByState, nullptr);
    primeResetFrontierReachabilitySolver(
        reachabilityContext,
        solverType,
        cubeAssignments(validationSupportCube),
        targetFrame);
  }

  size_t checkedClauses = 0;
  size_t deepResetSpecializedClauseChecks = 0;
  size_t learnedResetConflictClauses = 0;
  size_t learnedFreshResetConflictClauses = 0;
  size_t skippedDeepResetSpecializedProbes = 0;
  size_t freshResetSpecializedProbes = 0;
  std::vector<StateCube> residualExactValidationCubes;
  bool residualExactValidationOverflow = false;
  const bool deepPartialResetRepair =
      targetFrame > kMaxResetSpecializedBadFormulaValidationFrame &&
      !allowExactResetFrontierQueries;
  auto rememberResidualExactValidationCube = [&](const StateCube& cube) {
    if (allowExactResetFrontierQueries ||
        targetFrame >
            kMaxResidualExactResetCubeValidatedBadFormulaFrame ||
        validationSupportCube.size() > kMaxResetCubeValidationPrimeSupport) {
      return;
    }
    if (residualExactValidationCubes.size() <
        kMaxResidualExactResetCubeValidatedBadFormulaClauses) {
      residualExactValidationCubes.push_back(cube);
    } else {
      residualExactValidationOverflow = true;
    }
  };
  auto learnResetConflict = [&](StateCube conflict) -> bool {
    normalizeCube(conflict);
    rememberPdrAndResetFrontierUnreachableCore(
        resetFrontierCache,
        problem,
        transitionByState,
        conflict,
        targetFrame,
        nullptr);
    bool learnedFrameClause = false;
    if (frames != nullptr && targetFrame < frames->size() &&
        addClauseToFrame((*frames)[targetFrame], clauseFromCube(conflict))) {
      ++learnedResetConflictClauses;
      learnedFrameClause = true;
    }
    return learnedFrameClause;
  };
  auto reachedDeepPartialRepairBudget = [&]() {
    if (!deepPartialResetRepair) {
      return false;
    }
    if (deepResetSpecializedOnlyRepair) {
      // This path is cache-only: no fresh reset-image SAT query is opened, so
      // draining a batch is the fastest way to avoid rediscovering siblings.
      return learnedResetConflictClauses >=
             kMaxDeepCacheOnlyResetConflictClausesPerRepair;
    }
    return learnedFreshResetConflictClauses >=
           kMaxDeepPartialFreshResetConflictClausesPerRepair;
  };
  auto reachedNonExactFreshResetProbeBudget = [&]() {
    return !allowExactResetFrontierQueries &&
           freshResetSpecializedProbes >=
               kMaxNonExactFreshResetSpecializedProbesPerRepair;
  };
  auto scopedBadFormulaResetBudget =
      [&]() -> std::optional<ScopedResetSymbolicEvaluatorBudget> {
    if (allowExactResetFrontierQueries) {
      return std::nullopt;
    }
    return std::optional<ScopedResetSymbolicEvaluatorBudget>{
        std::in_place,
        resetSymbolicEvaluatorFor(
            resetFrontierCache, problem, transitionByState),
        kMaxBadFormulaRepairResetSymbolicStates,
        kMaxBadFormulaRepairResetSymbolicExprs};
  };
  for (const auto& clause : clauses) {
    const StateCube badCube = cubeForbiddenByStateClause(clause);
    if (const auto cachedCore =
            findPdrResetUnreachableCoreForCube(
                resetFrontierCache, badCube, targetFrame);
        cachedCore.has_value()) {
      learnResetConflict(*cachedCore);
      ++checkedClauses;
      if (reachedDeepPartialRepairBudget()) {
        break;
      }
      continue;
    }
    const size_t targetStep = problem.resetBootstrapCycles + targetFrame;
    if (deepResetSpecializedOnlyRepair) {
      // Deep bad-formula repair is a cache consumer only. Sampling on
      // BlackParrot showed that opening fresh reset-symbolic unrolls here can
      // dominate the whole PDR run; the ordinary concrete root validator still
      // performs exact checks and populates these caches when needed.
      if (const auto priorCoreConflict =
              memoizedPriorResetCoreConflictAtStep(
                  badCube,
                  targetFrame,
                  targetStep,
                  resetFrontierCache,
                  nullptr);
          priorCoreConflict.has_value()) {
        learnResetConflict(*priorCoreConflict);
        ++checkedClauses;
        if (reachedDeepPartialRepairBudget()) {
          break;
        }
        continue;
      }
      rememberResidualExactValidationCube(badCube);
      ++skippedDeepResetSpecializedProbes;
      continue;
    }
    if (reachedNonExactFreshResetProbeBudget()) {
      rememberResidualExactValidationCube(badCube);
      ++skippedDeepResetSpecializedProbes;
      continue;
    }
    ++freshResetSpecializedProbes;
    auto priorCoreBudget = scopedBadFormulaResetBudget();
    if (const auto priorCoreConflict =
            resetSpecializedPriorCoreConflictAtStep(
                problem,
                transitionByState,
                badCube,
                targetFrame,
                targetStep,
                resetFrontierCache,
                nullptr,
                allowExactResetFrontierQueries);
        priorCoreConflict.has_value()) {
      learnResetConflict(*priorCoreConflict);
      ++learnedFreshResetConflictClauses;
      ++checkedClauses;
      if (reachedDeepPartialRepairBudget()) {
        break;
      }
      continue;
    }
    if (reachedNonExactFreshResetProbeBudget()) {
      rememberResidualExactValidationCube(badCube);
      ++skippedDeepResetSpecializedProbes;
      continue;
    }
    ++freshResetSpecializedProbes;
    auto resetConflictBudget = scopedBadFormulaResetBudget();
    if (deepLocalResetSpecializedRepair) {
      ++deepResetSpecializedClauseChecks;
    }
    if (const auto resetConflict =
            resetSpecializedConflictCubeAtStep(
                problem,
                transitionByState,
                resetFrontierCache,
                badCube,
                targetStep,
                nullptr,
                allowExactResetFrontierQueries);
        resetConflict.has_value() && cubeContainsCube(badCube, *resetConflict)) {
      learnResetConflict(*resetConflict);
      ++learnedFreshResetConflictClauses;
      ++checkedClauses;
      if (reachedDeepPartialRepairBudget()) {
        break;
      }
      continue;
    }
    if (reachedNonExactFreshResetProbeBudget()) {
      rememberResidualExactValidationCube(badCube);
      ++skippedDeepResetSpecializedProbes;
      continue;
    }
    if (!allowExactResetFrontierQueries) {
      rememberResidualExactValidationCube(badCube);
      continue;
    }
    if (cubeReachableAtConcreteFrame(
            problem,
            solverType,
            transitionByState,
            badCube,
            targetFrame,
            resetFrontierCache,
            // This is a narrow validation of one bad assignment at the frame
            // where the new clauses will be learned. Use the shared exact
            // assumption solver and skip optional per-cube prechecks here:
            // BlackParrot sampling showed rebuilding those one-shot precheck
            // solvers dominating the validated-clause repair path.
            ConcreteCubeReachabilityMode::CachedAssumptions,
            nullptr,
            /*usePostBootstrapPrechecks=*/false)) {
      return false;
    }
    ++checkedClauses;
  }

  if (!allowExactResetFrontierQueries &&
      learnedResetConflictClauses == 0 &&
      !residualExactValidationOverflow &&
      !residualExactValidationCubes.empty()) {
    std::vector<std::vector<std::pair<size_t, bool>>> residualAssignments;
    residualAssignments.reserve(residualExactValidationCubes.size());
    for (const StateCube& residualCube : residualExactValidationCubes) {
      residualAssignments.push_back(cubeAssignments(residualCube));
    }
    auto& reachabilityContext = resetReachabilityContextFor(
        resetFrontierCache, problem, transitionByState, nullptr);
    const bool anyReachable =
        SEC::anyStateCubeReachableAtResetFrontier(
            reachabilityContext,
            solverType,
            residualAssignments,
            targetFrame,
            kResidualResetFrontierBatchConflictLimit,
            kResidualResetFrontierBatchPropagationLimit);
    if (anyReachable) {
      return false;
    }
    const size_t residualChecks = residualExactValidationCubes.size();
    checkedClauses += residualChecks;
    if (residualChecks != 0 && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: batched exact residual reset-cube "
          "bad-formula checks ",
          "bad_frame=", targetFrame,
          " clauses=", residualChecks,
          " total=", clauses.size());
    }
  }

  if (pdrStatsEnabled()) {
    emitSecDiag(
        allowExactResetFrontierQueries
            ? "SEC PDR stats: validated bad-formula clauses with reset cubes "
            : "SEC PDR stats: partially checked bad-formula reset conflicts ",
        "bad_frame=", targetFrame,
        " clauses=", checkedClauses,
        " total=", clauses.size(),
        " deep_probes=", deepResetSpecializedClauseChecks,
        " skipped_deep_probes=", skippedDeepResetSpecializedProbes,
        " fresh_reset_probes=", freshResetSpecializedProbes,
        " learned_reset_conflicts=", learnedResetConflictClauses);
  }
  if (learnedResetConflictClausesOut != nullptr) {
    *learnedResetConflictClausesOut = learnedResetConflictClauses;
  }
  if (checkedClauses != clauses.size()) {
    return std::nullopt;
  }
  return true;
}

KInductionProblem outputBadValidationProblem(
    const KInductionProblem& problem,
    const ObservedOutputBadClauseGroup& group) {
  KInductionProblem validationProblem = problem;
  validationProblem.observedOutputExprs0 = {
      problem.observedOutputExprs0[group.outputIndex]};
  validationProblem.observedOutputExprs1 = {
      problem.observedOutputExprs1[group.outputIndex]};
  validationProblem.observedOutputNames = {
      group.outputIndex < problem.observedOutputNames.size()
          ? problem.observedOutputNames[group.outputIndex]
          : std::to_string(group.outputIndex)};  // LCOV_EXCL_LINE
  validationProblem.bad = group.outputBad;
  validationProblem.property = BoolExpr::Not(group.outputBad);
  validationProblem.inductionBad = group.outputBad;
  validationProblem.inductionProperty = validationProblem.property;
  return validationProblem;
}

std::optional<bool> learnPartialTargetResetFrontierBadFormulaClauses(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant,
    const std::vector<StateClause>& clauses,
    std::vector<FrameClauses>& frames,
    size_t targetFrame,
    ResetFrontierCache& resetFrontierCache) {
  if (problem.resetBootstrapCycles == 0 || targetFrame == 0 ||
      targetFrame >= frames.size()) {
    return std::nullopt;
  }

  size_t cachedClauses = 0;
  size_t cheapChecks = 0;
  size_t learnedClauses = 0;
  for (const auto& clause : clauses) {
    if (frameHasSubsumingClause(frames[targetFrame], clause)) {
      continue;
    }

    const StateCube badCube = cubeForbiddenByStateClause(clause);
    if (const auto cachedCore =
            findPdrResetUnreachableCoreForCube(
                resetFrontierCache, badCube, targetFrame);
        cachedCore.has_value()) {
      if (addClauseToFrame(frames[targetFrame], clause)) {
        ++cachedClauses;
        ++learnedClauses;
      }
      continue;
    }

    if (cheapChecks >=
        kMaxPartialTargetResetFrontierBadFormulaCheapChecks) {
      continue;
    }

    ++cheapChecks;
    if (!cubeOutsideConcreteFrameByCheapResetFacts(
            problem,
            solverType,
            transitionByState,
            badCube,
            targetFrame,
            resetFrontierCache,
            frameInvariant)) {
      continue;
    }

    if (addClauseToFrame(frames[targetFrame], clause)) {
      ++learnedClauses;
    }
  }

  if (learnedClauses == 0) {
    return std::nullopt;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: refined projected counterexample with partial "
        "target-frame reset-frontier bad-formula clauses ",
        "bad_frame=", targetFrame,
        " clauses=", learnedClauses,
        " total=", clauses.size(),
        " cheap_checks=", cheapChecks,
        " cached_clauses=", cachedClauses);
  }
  return true;
}

std::optional<bool> learnPerOutputValidatedBadFormulaClauses(
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
    return std::nullopt;
  }

  bool learnedAnyClause = false;
  size_t checkedGroups = 0;
  size_t learnedClauses = 0;
  size_t learnedResetConflictClausesTotal = 0;
  for (const auto& group : groups) {
    const bool targetFrameOnlyRepair = targetFrame > 1;
    if (group.clauses.empty() ||
        group.clauses.size() > kMaxSingleOutputExactValidatedBadFormulaClauses ||
        (targetFrameOnlyRepair &&
         !hasNewValidatedBadFormulaClauseAtFrame(
             frames, group.clauses, targetFrame)) ||
        !hasNewValidatedBadFormulaClause(frames, group.clauses, targetFrame)) {
      continue;
    }

    ++checkedGroups;
    // The broad batch OR can be a hard SAT problem even when every individual
    // output mismatch is a tiny state-only predicate. Validate each output's
    // clauses separately, preferring the reset-cube validator because it reuses
    // the reset frontier SAT context across the whole batch.
    const KInductionProblem validationProblem =
        outputBadValidationProblem(problem, group);
    const bool allowExactResetValidation =
        targetFrame <= 1 &&
        group.clauses.size() <= kMaxExactResetCubeValidatedBadFormulaClauses;
    bool validatedGroup = false;
    size_t learnedResetConflictClauses = 0;
    if (const auto resetCubeValidation =
            validateBadFormulaClausesWithResetCubes(
                // Reset-cube validation only asks whether the forbidden state
                // assignments are reachable in the concrete transition system;
                // the output-local bad formula is not part of that SAT query.
                // Use the shared SEC problem/cache so per-output repair can
                // consume exact reset cores learned by root validation.
                problem,
                solverType,
                transitionByState,
                group.clauses,
                targetFrame,
                resetFrontierCache,
                &frames,
                &learnedResetConflictClauses,
                allowExactResetValidation);
        resetCubeValidation.has_value()) {
      if (!*resetCubeValidation) {
        return std::nullopt;
      }
      validatedGroup = true;
      if (learnedResetConflictClauses > 0) {
        learnedAnyClause = true;
      }
    }
    learnedResetConflictClausesTotal += learnedResetConflictClauses;
    bool validatedGroupAtTargetOnly = false;
    if (!validatedGroup &&
        !allowExactResetValidation &&
        learnedResetConflictClauses > 0) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: refined projected counterexample with per-output "
            "partial reset-cube conflict clauses ",
            "bad_frame=", targetFrame,
            " output=", group.outputIndex,
            " learned_reset_conflicts=", learnedResetConflictClauses);
      }
      return true;
    }
    if (!validatedGroup) {
      const StateCube validationSupportCube =
          validationSupportCubeForStateClauses(group.clauses);
      const bool allowBatchedResetFrontierValidation =
          problem.resetBootstrapCycles != 0 &&
          targetFrame <=
              (targetFrame > 1
                   ? kMaxPartialTargetResetFrontierBadFormulaFrame
                   : kMaxResetFrontierBatchedBadFormulaFrame) &&
          group.clauses.size() <=
              kMaxSingleOutputExactValidatedBadFormulaClauses &&
          !validationSupportCube.empty() &&
          validationSupportCube.size() <=
              kMaxResetFrontierBatchedBadFormulaSupport;
      if (allowBatchedResetFrontierValidation) {
        const bool useTargetFrameProof = targetFrame > 1;
        if (useTargetFrameProof) {
          if (const auto partialTargetRepair =
                  learnPartialTargetResetFrontierBadFormulaClauses(
                      problem,
                      solverType,
                      transitionByState,
                      frameInvariant,
                      group.clauses,
                      frames,
                      targetFrame,
                      resetFrontierCache);
              partialTargetRepair.has_value() && *partialTargetRepair) {
            return true;
          }
        } else {
          auto& reachabilityContext = resetReachabilityContextFor(
              resetFrontierCache, problem, transitionByState, frameInvariant);
          const auto forbiddenCubes = forbiddenAssignmentCubes(group.clauses);
          const bool anyReachable =
              SEC::anyStateCubeReachableWithinResetFrontier(
                  reachabilityContext,
                  solverType,
                  forbiddenCubes,
                  targetFrame);
          if (!anyReachable) {
            validatedGroup = true;
            validatedGroupAtTargetOnly = false;
            if (pdrStatsEnabled()) {
              emitSecDiag(
                  "SEC PDR stats: per-output batched reset-frontier ",
                  "bad-formula proof ",
                  "bad_frame=", targetFrame,
                  " output=", group.outputIndex,
                  " clauses=", group.clauses.size(),
                  " support=", validationSupportCube.size());
            }
          }
        }
      }
    }
    if (!validatedGroup && !allowExactResetValidation) {
      const size_t cachedResetValidatedAssignments =
          countCachedResetValidatedBadFormulaAssignments(
              group.clauses, targetFrame, resetFrontierCache);
      const bool allowWholeGroupAfterCachedRoot =
          targetFrame <=
              kMaxWholeBadFormulaBaseValidationAfterCachedRootFrame &&
          group.clauses.size() <=
              kMaxSingleOutputExactValidatedBadFormulaClauses &&
          cachedResetValidatedAssignments != 0;
      if (allowWholeGroupAfterCachedRoot) {
        const std::string validationKey =
            badFormulaValidationCacheKey(group.clauses, targetFrame);
        if (resetFrontierCache.wholeBadFormulaValidationMisses.find(
                validationKey) ==
            resetFrontierCache.wholeBadFormulaValidationMisses.end()) {
          if (pdrStatsEnabled()) {
            emitSecDiag(
                "SEC PDR stats: trying per-output whole bad-formula "
                "validation after cached reset roots ",
                "bad_frame=", targetFrame,
                " output=", group.outputIndex,
                " clauses=", group.clauses.size(),
                " cached_roots=", cachedResetValidatedAssignments);
          }
          if (SEC::provesNoBaseCounterexampleAtFrontier(
                  validationProblem, solverType, targetFrame)) {
            validatedGroup = true;
          } else {
            resetFrontierCache.wholeBadFormulaValidationMisses.insert(
                validationKey);
          }
        }
      }
    }
    if (!validatedGroup && !allowExactResetValidation) {
      continue;
    }
    if (!validatedGroup &&
        !SEC::provesNoBaseCounterexampleAtFrontier(
            validationProblem, solverType, targetFrame)) {
      return std::nullopt;
    }

    bool learnedGroupClause = false;
    for (const auto& clause : group.clauses) {
      const bool learnedClause =
          validatedGroupAtTargetOnly && targetFrame < frames.size()
              ? addClauseToFrame(frames[targetFrame], clause)
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
            "bad_frame=", targetFrame,
            " outputs=", checkedGroups,
            " clauses=", learnedClauses,
            " learned_reset_conflicts=", learnedResetConflictClausesTotal);
      }
      return true;
    }
  }

  if (!learnedAnyClause) {
    return std::nullopt;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: refined projected counterexample with per-output "
        "validated bad-formula clauses ",
        "bad_frame=", targetFrame,
        " outputs=", checkedGroups,
        " clauses=", learnedClauses,
        " learned_reset_conflicts=", learnedResetConflictClausesTotal);
  }
  return true;
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
  const auto outputBadClauseGroups =
      observedOutputBadFormulaClauseGroups(
          problem, transitionByState.stateSymbols());
  auto badClauses =
      observedOutputBadFormulaClauses(
          problem, transitionByState.stateSymbols());
  if (!badClauses.has_value()) {
    badClauses =
        stateOnlyBadFormulaClauses(problem.bad, transitionByState.stateSymbols());
  }
  if (!badClauses.has_value() || badClauses->empty()) {
    return std::nullopt;
  }
  const size_t exactValidatedBadFormulaClauseLimit =
      problem.observedOutputExprs0.size() == 1
          ? kMaxSingleOutputExactValidatedBadFormulaClauses
          : kMaxExactValidatedBadFormulaClauses;
  const bool useWholeBatchValidation =
      preferWholeBadFormulaValidation &&
      problem.observedOutputExprs0.size() > 1 &&
      badClauses->size() <= kMaxValidatedBadFormulaClauses;
  if (badClauses->size() > exactValidatedBadFormulaClauseLimit &&
      !useWholeBatchValidation) {
    if (badClauses->size() <= kMaxBatchResetCubeValidatedBadFormulaClauses &&
        hasNewValidatedBadFormulaClause(frames, *badClauses, targetFrame)) {
      size_t learnedResetConflictClauses = 0;
      const bool allowBroadExactResetValidation =
          targetFrame <= 1 &&
          badClauses->size() <=
              kMaxExactResetCubeValidatedBadFormulaClauses;
      if (const auto resetCubeValidation =
              validateBadFormulaClausesWithResetCubes(
                  problem,
                  solverType,
                  transitionByState,
                  *badClauses,
                  targetFrame,
                  resetFrontierCache,
                  &frames,
                  &learnedResetConflictClauses,
                  allowBroadExactResetValidation);
          resetCubeValidation.has_value() && *resetCubeValidation) {
        bool learnedAnyClause = false;
        for (const auto& clause : *badClauses) {
          learnedAnyClause =
              addClauseToFrames(frames, clause, targetFrame) ||
              learnedAnyClause;
        }
        if (learnedAnyClause || learnedResetConflictClauses > 0) {
          if (pdrStatsEnabled()) {
            emitSecDiag(
                "SEC PDR stats: refined projected counterexample with "
                "batched reset-cube validated bad-formula clauses ",
                "bad_frame=", targetFrame,
                " clauses=", badClauses->size(),
                " learned_reset_conflicts=", learnedResetConflictClauses);
          }
          return true;
        }
      }
      if (!allowBroadExactResetValidation &&
          learnedResetConflictClauses > 0) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample with "
              "partial reset-cube conflict clauses ",
              "bad_frame=", targetFrame,
              " learned_reset_conflicts=", learnedResetConflictClauses);
        }
        return true;
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
        frameInvariant,
        outputBadClauseGroups,
        frames,
        targetFrame,
        badFrame,
        resetFrontierCache);
  }

  // Do not spend another exact bounded-prefix solve when every candidate
  // clause is already present in the target frames. AES sampling showed PDR can
  // rediscover many neighboring abstract root cubes after the first repair, and
  // those duplicate validations dominated runtime while learning nothing.
  if (!hasNewValidatedBadFormulaClause(frames, *badClauses, targetFrame)) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: validated bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());
    }
    return std::nullopt;
  }
  if (targetFrame > 1 &&
      !hasNewValidatedBadFormulaClauseAtFrame(
          frames, *badClauses, targetFrame)) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: target bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());
    }
    return std::nullopt;
  }

  if (frameInvariantImpliesClauses(frameInvariant, solverType, *badClauses)) {
    bool learnedAnyClause = false;
    for (const auto& clause : *badClauses) {
      learnedAnyClause =
          addClauseToFrames(frames, clause, targetFrame) || learnedAnyClause;
    }
    if (learnedAnyClause && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: refined projected counterexample with "
          "frame-invariant implied bad-formula clauses ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());
    }
    return learnedAnyClause ? std::optional<bool>{true} : std::nullopt;
  }

  bool validatedBadClauses = false;
  bool validatedBadClausesAtTargetOnly = false;
  if (problem.observedOutputExprs0.size() == 1 &&
      badClauses->size() > kMaxExactValidatedBadFormulaClauses) {
    // A one-output state-only bad predicate can still enumerate to a few dozen
    // assignments. Sampling on BlackParrot showed one broad frontier proof for
    // that whole disjunction becoming the wall, while the concrete reset-cube
    // validator can reuse reset-specific caches and check each compact bad
    // assignment directly. This is still exact: every learned clause forbids
    // one assignment that was proven unreachable at the target frame.
    size_t learnedResetConflictClauses = 0;
    const bool allowExactResetValidation = false;
    if (const auto resetCubeValidation =
            validateBadFormulaClausesWithResetCubes(
                problem,
                solverType,
                transitionByState,
                *badClauses,
                targetFrame,
                resetFrontierCache,
                &frames,
                &learnedResetConflictClauses,
                allowExactResetValidation);
        resetCubeValidation.has_value()) {
      if (!*resetCubeValidation) {
        return std::nullopt;
      }
      validatedBadClauses = true;
      if (learnedResetConflictClauses > 0) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample with "
              "reset-cube conflict clauses ",
              "bad_frame=", targetFrame,
              " learned_reset_conflicts=", learnedResetConflictClauses);
        }
      }
    }
    if (!validatedBadClauses &&
        !allowExactResetValidation &&
        learnedResetConflictClauses > 0) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: refined projected counterexample with partial "
            "reset-cube conflict clauses ",
            "bad_frame=", targetFrame,
            " learned_reset_conflicts=", learnedResetConflictClauses);
      }
      return true;
    }
  }

  const StateCube validationSupportCube =
      validationSupportCubeForStateClauses(*badClauses);
  const bool allowBatchedResetFrontierValidation =
      !validatedBadClauses &&
      problem.resetBootstrapCycles != 0 &&
      problem.observedOutputExprs0.size() == 1 &&
      targetFrame <=
          (targetFrame > 1
               ? kMaxPartialTargetResetFrontierBadFormulaFrame
               : kMaxResetFrontierBatchedBadFormulaFrame) &&
      badClauses->size() <= kMaxSingleOutputExactValidatedBadFormulaClauses &&
      !validationSupportCube.empty() &&
      validationSupportCube.size() <=
          kMaxResetFrontierBatchedBadFormulaSupport;
  if (allowBatchedResetFrontierValidation) {
    const bool useTargetFrameProof = targetFrame > 1;
    if (useTargetFrameProof) {
      if (const auto partialTargetRepair =
              learnPartialTargetResetFrontierBadFormulaClauses(
                  problem,
                  solverType,
                  transitionByState,
                  frameInvariant,
                  *badClauses,
                  frames,
                  targetFrame,
                  resetFrontierCache);
          partialTargetRepair.has_value() && *partialTargetRepair) {
        return true;
      }
    } else {
      auto& reachabilityContext = resetReachabilityContextFor(
          resetFrontierCache, problem, transitionByState, frameInvariant);
      const auto forbiddenCubes = forbiddenAssignmentCubes(*badClauses);
      const bool anyReachable =
          SEC::anyStateCubeReachableWithinResetFrontier(
              reachabilityContext,
              solverType,
              forbiddenCubes,
              targetFrame);
      if (!anyReachable) {
        validatedBadClauses = true;
        validatedBadClausesAtTargetOnly = false;
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample with batched ",
              "reset-frontier bad-formula proof ",
              "bad_frame=", targetFrame,
              " clauses=", badClauses->size(),
              " support=", validationSupportCube.size());
        }
      }
    }
  }

  const size_t cachedResetValidatedAssignments =
      problem.observedOutputExprs0.size() == 1
          ? countCachedResetValidatedBadFormulaAssignments(
                *badClauses, targetFrame, resetFrontierCache)
          : 0;
  const bool allowDeepWholeBadFormulaAfterCachedRoot =
      problem.observedOutputExprs0.size() == 1 &&
      targetFrame <=
          kMaxWholeBadFormulaBaseValidationAfterCachedRootFrame &&
      badClauses->size() <= kMaxSingleOutputExactValidatedBadFormulaClauses &&
      cachedResetValidatedAssignments != 0;
  const bool allowWholeBadFormulaBaseValidation =
      useWholeBatchValidation ||
      targetFrame <= kMaxWholeBadFormulaBaseValidationFrame ||
      badClauses->size() <= kMaxExactValidatedBadFormulaClauses ||
      allowDeepWholeBadFormulaAfterCachedRoot;
  if (!validatedBadClauses && !allowWholeBadFormulaBaseValidation) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: skipped deep bad-formula base validation ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());
    }
    return std::nullopt;
  }

  // Prove the bad formula unreachable as a whole before learning its
  // state-only blocking clauses when the reset-cube path is unavailable and
  // the query is still local. This is an exact CEGAR repair: the clauses are
  // learned only after the bounded base-case check proves the one-output bad
  // predicate itself is unreachable at the target frontier.
  if (!validatedBadClauses) {
    const std::string validationKey =
        badFormulaValidationCacheKey(*badClauses, targetFrame);
    if (allowDeepWholeBadFormulaAfterCachedRoot &&
        resetFrontierCache.wholeBadFormulaValidationMisses.find(validationKey) !=
            resetFrontierCache.wholeBadFormulaValidationMisses.end()) {
      return std::nullopt;
    }
    if (allowDeepWholeBadFormulaAfterCachedRoot && pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: trying deep whole bad-formula validation after "
          "cached reset roots ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size(),
          " cached_roots=", cachedResetValidatedAssignments);
    }
    const bool badFormulaUnreachable =
        useWholeBatchValidation
            ? SEC::provesNoBaseCounterexampleAtFrontierWithSecConeProof(
                  problem, solverType, targetFrame)
            : SEC::provesNoBaseCounterexampleAtFrontier(
                  problem, solverType, targetFrame);
    if (!badFormulaUnreachable) {
      if (allowDeepWholeBadFormulaAfterCachedRoot) {
        resetFrontierCache.wholeBadFormulaValidationMisses.insert(validationKey);
      }
      return std::nullopt;
    }
  }

  bool learnedAnyClause = false;
  for (const auto& clause : *badClauses) {
    learnedAnyClause =
        (validatedBadClausesAtTargetOnly && targetFrame < frames.size()
             ? addClauseToFrame(frames[targetFrame], clause)
             : addClauseToFrames(frames, clause, targetFrame)) ||
        learnedAnyClause;
  }
  if (!learnedAnyClause) {
    // If all validated bad-formula clauses were already present, claiming a
    // refinement would make PDR rediscover the same bad cube forever.  Let the
    // caller try the concrete root-cube refinement or report an abstract
    // counterexample for the SEC strategy to split/validate.
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: validated bad-formula clauses already present ",
          "bad_frame=", targetFrame,
          " clauses=", badClauses->size());
    }
    return std::nullopt;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: refined projected counterexample with validated "
        "bad-formula clauses ",
        "bad_frame=", targetFrame,
        " clauses=", badClauses->size());
  }
  return true;
}

void addStateClause(SATSolverWrapper& solver,
                    const FrameVariableStore& variables,
                    const StateClause& clause,
                    size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(clause.size());
  for (const auto& literal : clause) {
    const int satLiteral = variables.getLiteral(literal.symbol, frame);
    satClause.push_back(literal.positive ? satLiteral : -satLiteral);
  }
  solver.addClause(satClause);
}

bool clauseCoveredByVariables(const FrameVariableStore& variables,
                              const StateClause& clause) {
  for (const auto& literal : clause) {
    if (!variables.hasSymbol(literal.symbol)) {
      return false;
    }
  }
  return true;
}

uint64_t nextClauseEmitEpoch(const FrameClauses& frameClauses) {
  if (frameClauses.clauseEmitEpochByIndex.size() !=
      frameClauses.clauses.size()) {
    frameClauses.clauseEmitEpochByIndex.assign(
        frameClauses.clauses.size(), 0);
  }
  ++frameClauses.clauseEmitEpoch;
  if (frameClauses.clauseEmitEpoch == 0) {
    // Practically unreachable, but keep the epoch scheme correct even after an
    // absurd number of local PDR queries.
    std::fill(
        frameClauses.clauseEmitEpochByIndex.begin(),
        frameClauses.clauseEmitEpochByIndex.end(),
        0);
    frameClauses.clauseEmitEpoch = 1;
  }
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
  const size_t maxProjectedFrameLiterals = maxProjectedFrameLiteralsPerQuery();
  for (const auto symbol : querySymbols) {
    if (emittedClauses >= maxProjectedFrameClauses ||
        emittedLiterals >= maxProjectedFrameLiterals) {
      break;
    }
    const auto indexIt = frameClauses.clauseIndicesBySymbol.find(symbol);
    if (indexIt == frameClauses.clauseIndicesBySymbol.end()) {
      continue;
    }
    for (const auto clauseIndex : indexIt->second) {
      if (emittedClauses >= maxProjectedFrameClauses ||
          emittedLiterals >= maxProjectedFrameLiterals) {
        return;
      }
      if (frameClauses.clauseEmitEpochByIndex[clauseIndex] == emitEpoch) {
        continue;
      }
      frameClauses.clauseEmitEpochByIndex[clauseIndex] = emitEpoch;
      const auto& clause = frameClauses.clauses[clauseIndex];
      if (!clauseCoveredByVariables(variables, clause)) {
        continue;
      }
      if (clause.size() > maxProjectedFrameLiterals) {
        continue;
      }
      if (emittedLiterals + clause.size() > maxProjectedFrameLiterals &&
          emittedClauses != 0) {
        continue;
      }
      addStateClause(solver, variables, clause, frame);
      ++emittedClauses;
      emittedLiterals += clause.size();
    }
  }
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
    if (!clauseCoveredByVariables(variables, clause)) {
      continue;  // LCOV_EXCL_LINE
    }
    addStateClause(solver, variables, clause, frame);
  }
}

void addCubeAssumptions(SATSolverWrapper& solver,
                        const FrameVariableStore& variables,
                        const StateCube& cube,
                        size_t frame) {
  for (const auto& literal : cube) {
    solver.addClause(
        {literal.value ? variables.getLiteral(literal.symbol, frame)
                       : -variables.getLiteral(literal.symbol, frame)});
  }
}

void addNegatedCubeClause(SATSolverWrapper& solver,
                          const FrameVariableStore& variables,
                          const StateCube& cube,
                          size_t frame) {
  std::vector<int> satClause;
  satClause.reserve(cube.size());
  for (const auto& literal : cube) {
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
    }
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
    return;
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
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

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
    if (!emittedStructuredInit && initFormula != nullptr &&
        !hasStructuredInitFacts(problem)) {
      // Observation-only startups have no per-symbol structured summary, so
      // the exact init formula must remain as the F[0] fallback. When
      // structured init facts do exist, an empty relevant subset simply means
      // the local cone is unconstrained by Init; falling back to the full
      // monolithic init formula would reintroduce unrelated symbols into a
      // reduced compact-PDR query and can make the encoder reference leaves
      // that were intentionally left out of the local solver.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      try {
        solver.addClause({encoder.encode(initFormula)});
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR init-frame encoding failed at frame " + std::to_string(frame) +
            ": " + error.what());
      }
    }
    if (problem.resetBootstrapCycles != 0 && problem.property != nullptr) {
      // The concrete reset/bootstrap check at the start of run() proves that
      // F[0] satisfies the current SEC property slice.  Structured init
      // encoding otherwise bypasses initFormula, so encode that checked
      // property explicitly for level-0 predecessor queries.
      FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));
      try {
        solver.addClause({encoder.encode(problem.property)});
      } catch (const std::runtime_error& error) {
        throw std::runtime_error(
            "PDR reset-frame property encoding failed at frame " +
            std::to_string(frame) + ": " + error.what());
      }
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
  // any validated strengthening invariant the strategy handed to PDR.
  if (exactFrameClauses) {
    addAllFrameClauses(solver, variables, frames[level], frame);
  } else {
    addIndexedFrameClauses(solver, variables, frames[level], querySymbols, frame);
  }
  if (frameInvariant != nullptr) {
    // The optional strengthening is treated exactly like a frame fact, but it
    // is validated before we allow the engine to rely on it.
    FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
    try {  // LCOV_EXCL_LINE
      solver.addClause({encoder.encode(frameInvariant)});  // LCOV_EXCL_LINE
    } catch (const std::runtime_error& error) {  // LCOV_EXCL_LINE
      throw std::runtime_error(  // LCOV_EXCL_LINE
          "PDR frame invariant encoding failed at frame " +
          std::to_string(frame) + ": " + error.what());  // LCOV_EXCL_LINE
    }  // LCOV_EXCL_LINE
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
                                    size_t frame) {
  if (!predecessorSourceFrameIsKnownSafe(level) || problem.property == nullptr) {
    return;
  }
  // Projected frame clauses intentionally omit unrelated learned clauses to
  // keep ASIC predecessor queries local. The property is the one frame fact we
  // must not let projection forget for already-safe frames; adding it is
  // logically redundant for exact PDR, but avoids fake init-reaching paths
  // that then need expensive concrete reset-frontier validation.
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(frame));  // LCOV_EXCL_LINE
  try {  // LCOV_EXCL_LINE
    solver.addClause({encoder.encode(problem.property)});  // LCOV_EXCL_LINE
  } catch (const std::runtime_error& error) {  // LCOV_EXCL_LINE
    throw std::runtime_error(  // LCOV_EXCL_LINE
        "PDR safe-frame property encoding failed at frame " +
        std::to_string(frame) + ": " + error.what());  // LCOV_EXCL_LINE
  }  // LCOV_EXCL_LINE
}

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
  std::vector<size_t> worklist;
  worklist.reserve(assignments.size());
  for (const auto& [symbol, value] : assignments) {
    (void)value;
    worklist.push_back(symbol);
  }

  for (size_t index = 0; index < worklist.size(); ++index) {
    const size_t symbol = worklist[index];
    const auto partnersIt = complementPartners.partnersBySymbol.find(symbol);
    if (partnersIt == complementPartners.partnersBySymbol.end()) {
      continue;
    }
    if (!variables.hasSymbol(symbol)) {
      continue;  // LCOV_EXCL_LINE
    }
    for (const auto partnerSymbol : partnersIt->second) {
      if (assignments.find(partnerSymbol) != assignments.end() ||
          !variables.hasSymbol(partnerSymbol)) {
        continue;
      }
      assignments[partnerSymbol] =
          solver.getLiteralValue(variables.getLiteral(partnerSymbol, frame));
      worklist.push_back(partnerSymbol);
    }
  }
}

bool formulaModelValue(const SATSolverWrapper& solver,
                       const std::unordered_map<size_t, int>& leafLits,
                       BoolExpr* formula,
                       std::unordered_map<BoolExpr*, bool>& memo) {
  if (formula == nullptr) {
    return false;  // LCOV_EXCL_LINE
  }
  if (const auto it = memo.find(formula); it != memo.end()) {
    return it->second;
  }

  bool value = false;
  switch (formula->getOp()) {
    case Op::VAR:
      if (formula->getId() == 0) {
        value = false;
      } else if (formula->getId() == 1) {
        value = true;
      } else {
        value = solver.getLiteralValue(leafLits.at(formula->getId()));
      }
      break;
    case Op::NOT:
      value = !formulaModelValue(
          solver, leafLits, formula->getLeft(), memo);
      break;
    case Op::AND:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) &&
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::OR:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) ||
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::XOR:
      value = formulaModelValue(
                  solver, leafLits, formula->getLeft(), memo) ^
              formulaModelValue(
                  solver, leafLits, formula->getRight(), memo);
      break;
    case Op::NONE:
    default:
      value = false;  // LCOV_EXCL_LINE
      break;
  }
  memo.emplace(formula, value);
  return value;
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
          valueMemo,
          assignments,
          budget);
      return;
    case Op::AND:
      if (desiredValue) {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), true,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), true,
            stateSymbols, valueMemo, assignments, budget);
      } else {
        const bool leftValue = formulaModelValue(
            solver, leafLits, formula->getLeft(), valueMemo);
        addJustifyingStateLiterals(
            solver,
            leafLits,
            leftValue ? formula->getRight() : formula->getLeft(),
            false,
            stateSymbols,
            valueMemo,
            assignments,
            budget);
      }
      return;
    case Op::OR:
      if (desiredValue) {
        const bool leftValue = formulaModelValue(
            solver, leafLits, formula->getLeft(), valueMemo);
        addJustifyingStateLiterals(
            solver,
            leafLits,
            leftValue ? formula->getLeft() : formula->getRight(),
            true,
            stateSymbols,
            valueMemo,
            assignments,
            budget);
      } else {
        addJustifyingStateLiterals(
            solver, leafLits, formula->getLeft(), false,
            stateSymbols, valueMemo, assignments, budget);
        addJustifyingStateLiterals(
            solver, leafLits, formula->getRight(), false,
            stateSymbols, valueMemo, assignments, budget);
      }
      return;
    case Op::XOR: {
      const bool leftValue = formulaModelValue(
          solver, leafLits, formula->getLeft(), valueMemo);
      const bool rightValue = formulaModelValue(
          solver, leafLits, formula->getRight(), valueMemo);
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
    case Op::NONE:
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
  JustificationBudget budget{
      std::max(
          kMinPredecessorJustificationVisits,
          maxAssignments * kPredecessorJustificationVisitMultiplier),
      maxAssignments,
      false};
  const auto& stateSymbols = transitionByState.stateSymbols();
  const auto& primaryByComplement = transitionByState.primaryByComplement();

  for (const auto& literal : targetCube) {
    size_t transitionSymbol = literal.symbol;
    bool desiredValue = literal.value;
    if (!transitionByState.contains(transitionSymbol)) {
      const auto primaryIt = primaryByComplement.find(transitionSymbol);
      if (primaryIt == primaryByComplement.end() ||
          !transitionByState.contains(primaryIt->second)) {
        continue;
      }
      // The target names a complemented flop output. The transition relation
      // is encoded on the primary flop, and addComplementedStateRelations()
      // constrains the complemented next-state literal to be its inverse.
      transitionSymbol = primaryIt->second;
      desiredValue = !desiredValue;
    }

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
    bool exactFrameClauses) {
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
          exactFrameClauses);
  SATSolverWrapper solver(solverType);
  // The bad-state query is not the repeated predecessor obligation that makes
  // PDR sensitive to solver startup overhead. It is a frame-level cone proof
  // over the current output slice, so Kissat's normal SEC cone profile may use
  // preprocessing/congruence when that helps collapse duplicated miter logic.
  solver.configureForSecConeProof(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  addFrameConstraints(
      solver, variables, problem, initFormula, frameInvariant, frames, level, 0,
      solverSymbols, exactFrameClauses);
  addPostBootstrapResetInputConstraints(solver, variables, problem, 0);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  try {
    solver.addClause({encoder.encode(badFormula)});
  } catch (const std::runtime_error& error) {
    throw std::runtime_error(
        "PDR bad-state encoding failed at level " + std::to_string(level) +
        ": " + error.what());
  }
  if (!solver.solve()) {
    return std::nullopt;
  }

  // Start with the full state support when it is bounded.  That gives PDR a
  // precise bad obligation instead of a tiny projection that can mix unrelated
  // state valuations and later look like a counterexample only in the abstract.
  if (preciseBadStateSupport.has_value() && !preciseBadStateSupport->empty()) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR bad cube uses precise state support: ",
          preciseBadStateSupport->size(),
          " state symbols at F",
          level);
    }
    StateCube cube = boundedPrefixCube(
        extractStateCube(solver, variables, *preciseBadStateSupport, 0),
        structuralBadProjectionLimit);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: bad cube level=", level,
          " source=precise support=", preciseBadStateSupport->size(),
          " cube=", cube.size(),
          " hash=", cubeFingerprint(cube),
          " limit=", structuralBadProjectionLimit);
    }
    return cube;
  } else if (isSecDiagEnabled()) {
    emitSecDiag(
        "SEC diag: PDR bad cube falls back to structural justification at F",
        level,
        " after support budget ",
        kMaxPreciseBadCubeSupportNodes);
  }

  // Very large ASIC datapaths still need a compact fallback: extracting every
  // state bit in the bad cone would force every later predecessor query to
  // encode the transition for all of those latches.  The structural
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
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bad cube level=", level,
        " source=structural cube=", cube.size(),
        " hash=", cubeFingerprint(cube),
        " limit=", structuralBadProjectionLimit);
  }
  return cube;
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
                                     bool exactFrameClauses) {
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
        exactFrameClauses);
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
            exactFrameClauses);
        cube.has_value()) {
      return cube;
    }
  }
  return std::nullopt;
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
    const std::vector<StateClause>* extraFrameClauses = nullptr,
    size_t* predecessorQueryBudget = nullptr,
    bool useExactResetFrontierChecks = true) {
  // This is the one-step predecessor query at the heart of PDR: does some
  // state in F[level] transition into the target cube on the next frame?
  consumePdrPredecessorQueryBudget(predecessorQueryBudget);
  const std::vector<size_t> targetSymbols = cubeStateSymbols(targetCube);
  const std::vector<size_t> encodedTargets =
      expandTransitionTargets(problem, targetSymbols, transitionByState);
  const std::vector<size_t> transitionSupportSymbols =
      collectTransitionSupportSymbols(transitionByState, encodedTargets);
  const size_t statsQueryNumber = nextPdrPredecessorQueryNumber();
  const bool emitStatsForQuery = shouldEmitPdrStats(statsQueryNumber);
  const bool predecessorQueryIsAlreadyExact = predecessorProjectionLimit == 0;
  const size_t exactResetPrecheckSupportLimit =
      maxExactResetPrecheckTransitionSupport(solverType);

  // This reset-frontier precheck is an optional accelerator for projected PDR
  // queries: it can reject fake F[0] predecessors before they become root
  // obligations. In unprojected mode the predecessor query itself is already
  // the cheapest exact PDR step available, and AES sampling showed the extra
  // reset-prefix SAT precheck becoming the wall before that query could run.
  if (useExactResetFrontierChecks &&
      !predecessorQueryIsAlreadyExact &&
      level == 0 && problem.resetBootstrapCycles != 0 &&
      resetFrontierCache != nullptr &&
      transitionSupportSymbols.size() <= exactResetPrecheckSupportLimit) {
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
          " support_limit=", exactResetPrecheckSupportLimit,
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
        " support_limit=", exactResetPrecheckSupportLimit,
        " exact_reset_frontier=",
        useExactResetFrontierChecks ? "skipped" : "disabled");
  }

  const std::vector<size_t> predecessorSymbols = predecessorProjectionSymbols(
      problem,
      transitionByState,
      initFormula,
      frameInvariant,
      frames,
      level,
      complementPartners,
      transitionSupportSymbols);
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
      extraFrameClauses);
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
        " projection_limit=", predecessorProjectionLimit,
        " frame_clauses=",
        level < frames.size() ? frames[level].clauses.size() : 0,
        " exclude_target=", excludeTargetOnCurrentFrame ? 1 : 0);
  }
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
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
  const bool hasPredecessor = solver.solve();
  if (emitStatsForQuery) {
    emitSecDiag(
        "SEC PDR stats: predecessor #", statsQueryNumber,
        " result=", hasPredecessor ? "sat" : "unsat");
  }
  if (!hasPredecessor) {
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
      initIntersectionSymbols(problem, initFormula, cube);
  SATSolverWrapper solver(solverType);
  solver.configureForSecPdrQuery(solverSymbols.size());
  FrameVariableStore variables(solver, solverSymbols, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 1);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 1);
  FrameFormulaEncoder encoder(solver, variables.makeLeafLits(0));
  solver.addClause({encoder.encode(initFormula)});
  addCubeAssumptions(solver, variables, cube, 0);
  return solver.solve();
}

bool appendTargetLiteral(StateCube& candidate,
                         const StateCube& targetCube,
                         size_t symbol) {
  if (findCubeLiteralValue(candidate, symbol).has_value()) {
    return false;
  }
  const auto targetValue = findCubeLiteralValue(targetCube, symbol);
  if (!targetValue.has_value()) {
    return false;
  }
  candidate.push_back({symbol, *targetValue});
  normalizeCube(candidate);
  return true;
}

size_t cubeLiteralKey(const CubeLiteral& literal) {
  return (literal.symbol << 1) | (literal.value ? 1u : 0u);
}

std::vector<int> assumptionLiteralsForCube(
    const StateCube& cube,
    const std::vector<std::pair<int, CubeLiteral>>& assumptionPairs) {
  std::unordered_map<size_t, int> assumptionByLiteral;
  assumptionByLiteral.reserve(assumptionPairs.size());
  for (const auto& [assumptionLit, literal] : assumptionPairs) {
    assumptionByLiteral.emplace(cubeLiteralKey(literal), assumptionLit);
  }

  std::vector<int> assumptions;
  assumptions.reserve(cube.size());
  for (const auto& literal : cube) {
    const auto it = assumptionByLiteral.find(cubeLiteralKey(literal));
    if (it == assumptionByLiteral.end()) {
      assumptions.clear();
      return assumptions;
    }
    assumptions.push_back(it->second);
  }
  return assumptions;
}

StateCube cubeFromAssumptionLiterals(
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption) {
  StateCube cube;
  cube.reserve(assumptions.size());
  for (const auto assumption : assumptions) {
    const auto it = literalByAssumption.find(assumption);
    if (it == literalByAssumption.end()) {
      cube.clear();
      return cube;
    }
    cube.push_back(it->second);
  }
  normalizeCube(cube);
  return cube;
}

std::optional<StateCube> minimizeCoreInTargetContext(
    SATSolverWrapper& coreSolver,
    const std::vector<int>& assumptions,
    const std::unordered_map<int, CubeLiteral>& literalByAssumption,
    size_t* checks) {
  std::vector<int> candidate = assumptions;
  if (candidate.empty()) {
    return std::nullopt;
  }

  for (size_t chunkSize = std::max<size_t>(1, candidate.size() / 2);
       chunkSize > 0 &&
       *checks < kMaxPredecessorCoreContextMinimizationChecks;) {
    bool removedAny = false;
    for (size_t index = 0;
         index < candidate.size() &&
         *checks < kMaxPredecessorCoreContextMinimizationChecks;) {
      const size_t erasedCount =
          std::min(chunkSize, candidate.size() - index);
      if (erasedCount == 0 || erasedCount == candidate.size()) {
        break;
      }

      std::vector<int> trial = candidate;
      trial.erase(
          trial.begin() + static_cast<std::ptrdiff_t>(index),
          trial.begin() +
              static_cast<std::ptrdiff_t>(index + erasedCount));
      ++(*checks);
      const auto status = coreSolver.solveWithAssumptionsStatus(
          trial, kPredecessorCoreConflictLimit);
      if (status == SATSolverWrapper::SolveStatus::Unsat) {
        candidate = std::move(trial);
        removedAny = true;
        continue;
      }
      index += erasedCount;
    }

    if (chunkSize == 1) {
      break;
    }
    if (!removedAny && chunkSize == 1) {
      break;
    }
    chunkSize = std::max<size_t>(1, chunkSize / 2);
  }

  StateCube minimized = cubeFromAssumptionLiterals(
      candidate, literalByAssumption);
  if (minimized.empty()) {
    return std::nullopt;
  }
  return minimized;
}

std::optional<StateCube> growCoreOutsideInit(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    BoolExpr* initFormula,
    const StateCube& core,
    const StateCube& targetCube) {
  StateCube candidate = core;
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {
    return candidate;
  }

  auto tryAddSymbol = [&](size_t symbol) -> bool {
    if (!appendTargetLiteral(candidate, targetCube, symbol)) {
      return false;
    }
    return !cubeIntersectsInit(problem, solverType, initFormula, candidate);
  };

  const bool usesBootstrapFrontier = problem.resetBootstrapCycles != 0;
  const auto& assignments = usesBootstrapFrontier
                                ? problem.bootstrapStateAssignments
                                : problem.initialStateAssignments;
  const auto& equalities = usesBootstrapFrontier
                               ? problem.bootstrapStateEqualityPairs
                               : problem.initialStateEqualityPairs;

  // UNSAT cores from transition assumptions can be too small to be legal PDR
  // frame clauses because a one-bit reason may still overlap Init. Add only
  // original target literals until the cube visibly contradicts Init; the
  // predecessor UNSAT result is monotonic under this strengthening.
  for (const auto& [symbol, initValue] : assignments) {
    const auto targetValue = findCubeLiteralValue(targetCube, symbol);
    if (targetValue.has_value() && *targetValue != initValue &&
        tryAddSymbol(symbol)) {
      return candidate;
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);
    if (!lhsTargetValue.has_value() || !rhsTargetValue.has_value() ||
        *lhsTargetValue == *rhsTargetValue) {
      continue;
    }
    if (tryAddSymbol(lhsSymbol) || tryAddSymbol(rhsSymbol)) {
      return candidate;
    }
  }
  for (const auto& [lhsSymbol, rhsSymbol] : equalities) {
    const auto lhsCoreValue = findCubeLiteralValue(candidate, lhsSymbol);
    const auto rhsCoreValue = findCubeLiteralValue(candidate, rhsSymbol);
    const auto lhsTargetValue = findCubeLiteralValue(targetCube, lhsSymbol);
    const auto rhsTargetValue = findCubeLiteralValue(targetCube, rhsSymbol);
    if (lhsCoreValue.has_value() && rhsTargetValue.has_value() &&
        *lhsCoreValue != *rhsTargetValue && tryAddSymbol(rhsSymbol)) {
      return candidate;
    }
    if (rhsCoreValue.has_value() && lhsTargetValue.has_value() &&
        *rhsCoreValue != *lhsTargetValue && tryAddSymbol(lhsSymbol)) {
      return candidate;
    }
  }
  if (problem.complementedStatePairs0.size() <=
      kMaxComplementPairsForCheapInitCheck) {
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs0) {
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (!primaryTargetValue.has_value() ||
          !complementedTargetValue.has_value() ||
          *primaryTargetValue != *complementedTargetValue) {
        continue;
      }
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs0) {
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&
          *primaryCoreValue == *complementedTargetValue &&
          tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&
          *complementedCoreValue == *primaryTargetValue &&
          tryAddSymbol(primarySymbol)) {
        return candidate;
      }
    }
  }
  if (problem.complementedStatePairs1.size() <=
      kMaxComplementPairsForCheapInitCheck) {
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs1) {
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (!primaryTargetValue.has_value() ||
          !complementedTargetValue.has_value() ||
          *primaryTargetValue != *complementedTargetValue) {
        continue;
      }
      if (tryAddSymbol(primarySymbol) || tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
    }
    for (const auto& [primarySymbol, complementedSymbol] :
         problem.complementedStatePairs1) {
      const auto primaryCoreValue =
          findCubeLiteralValue(candidate, primarySymbol);
      const auto complementedCoreValue =
          findCubeLiteralValue(candidate, complementedSymbol);
      const auto primaryTargetValue =
          findCubeLiteralValue(targetCube, primarySymbol);
      const auto complementedTargetValue =
          findCubeLiteralValue(targetCube, complementedSymbol);
      if (primaryCoreValue.has_value() && complementedTargetValue.has_value() &&
          *primaryCoreValue == *complementedTargetValue &&
          tryAddSymbol(complementedSymbol)) {
        return candidate;
      }
      if (complementedCoreValue.has_value() && primaryTargetValue.has_value() &&
          *complementedCoreValue == *primaryTargetValue &&
          tryAddSymbol(primarySymbol)) {
        return candidate;
      }
    }
  }

  for (const auto& literal : targetCube) {
    if (tryAddSymbol(literal.symbol)) {
      return candidate;
    }
  }
  if (!cubeIntersectsInit(problem, solverType, initFormula, candidate)) {
    return candidate;
  }
  return std::nullopt;
}

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
    const ComplementPartnerIndex& complementPartners,
    size_t predecessorProjectionLimit,
    bool exactFrameClauses,
    bool useExactResetFrontierChecks,
    size_t* predecessorQueryBudget) {
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
      transitionSupportSymbols);
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
      nullptr);

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
  addFrameConstraints(
      coreSolver,
      variables,
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
  if (excludeCurrentTargetForCore) {
    addNegatedCubeClause(coreSolver, variables, targetCube, 0);
  }

  const auto assumptionPairs = addTransitionAssumptionsForTargetCube(
      coreSolver,
      variables,
      transitionByState,
      0,
      targetCube,
      encodedTargets,
      transitionSupportSymbols);
  if (assumptionPairs.empty()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=empty_assumptions target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  std::vector<int> assumptions;
  assumptions.reserve(assumptionPairs.size());
  std::unordered_map<int, CubeLiteral> literalByAssumption;
  literalByAssumption.reserve(assumptionPairs.size() * 2);
  for (const auto& [assumptionLit, cubeLiteral] : assumptionPairs) {
    assumptions.push_back(assumptionLit);
    literalByAssumption.emplace(assumptionLit, cubeLiteral);
    // Assumption-core solvers may report final conflicts in solver-literal polarity. Map both
    // signs back to the requested cube literal and let exact revalidation below
    // decide whether the proposed core is usable.
    literalByAssumption.emplace(-assumptionLit, cubeLiteral);
  }

  const auto coreQueryStatus = coreSolver.solveWithAssumptionsStatus(
      assumptions, kPredecessorCoreConflictLimit);
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Sat) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=core_query_sat target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }
  if (coreQueryStatus == SATSolverWrapper::SolveStatus::Unknown) {
    if (pdrStatsEnabled() &&
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=resource_limit target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  StateCube core;
  const auto failedAssumptions = coreSolver.failedAssumptions();
  for (const auto failedLit : failedAssumptions) {
    const auto it = literalByAssumption.find(failedLit);
    if (it == literalByAssumption.end()) {
      continue;
    }
    core.push_back(it->second);
  }
  normalizeCube(core);
  if (core.empty() || core.size() >= targetCube.size()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=not_smaller target=",
          targetCube.size(),
          " source_level=",
          sourceLevel,
          " failed_assumptions=",
          failedAssumptions.size(),
          " mapped_core=",
          core.size(),
          " target_hash=",
          cubeFingerprint(targetCube));
    }
    return std::nullopt;
  }

  if (sourceLevel != 0) {
    // For higher frames the generalized clause is pushed into earlier learned
    // frames as well, so keep the standard IC3/PDR requirement that the reduced
    // cube excludes Init.  Source level zero is different in this implementation:
    // F0 is the already-checked startup frontier and the learned clause is only
    // placed in F1, so the exact no-predecessor query from F0 is the required
    // safety check.  BlackParrot sampling showed thousands of repeated
    // source_level=0 core misses when we unnecessarily rejected those cores for
    // overlapping Init.
    const auto initSafeCore = growCoreOutsideInit(
        problem, solverType, initFormula, core, targetCube);
    if (!initSafeCore.has_value() || initSafeCore->size() >= targetCube.size()) {
      if (pdrStatsEnabled() &&
          targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
        emitSecDiag(
            "SEC PDR stats: predecessor core miss reason=init_intersection target=",
            targetCube.size(),
            "->",
            core.size(),
            " source_level=",
            sourceLevel,
            " target_hash=",
            cubeFingerprint(targetCube),
            " core_hash=",
            cubeFingerprint(core));
      }
      return std::nullopt;
    }
    core = *initSafeCore;
  }

  std::vector<int> coreAssumptions =
      assumptionLiteralsForCube(core, assumptionPairs);
  bool coreBlockedInTargetContext = false;
  bool coreContextResourceLimited = false;
  if (coreAssumptions.size() == core.size()) {
    const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(
        coreAssumptions, kPredecessorCoreConflictLimit);
    coreBlockedInTargetContext =
        coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;
    coreContextResourceLimited =
        coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;
  }
  size_t contextMinimizationChecks = 0;
  if (!coreBlockedInTargetContext &&
      !coreContextResourceLimited &&
      targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // The failed-assumption vector is only a seed. If it is not itself UNSAT,
    // minimize the full target assumption set in the same solver context. This
    // keeps the proof obligation honest: every accepted reduced cube is backed
    // by an actual UNSAT predecessor query, not by solver-conflict bookkeeping.
    if (const auto minimizedCore = minimizeCoreInTargetContext(
            coreSolver,
            assumptions,
            literalByAssumption,
            &contextMinimizationChecks);
        minimizedCore.has_value() &&
        minimizedCore->size() < targetCube.size()) {
      core = *minimizedCore;
      coreAssumptions = assumptionLiteralsForCube(core, assumptionPairs);
      if (coreAssumptions.size() == core.size()) {
        const auto coreContextStatus = coreSolver.solveWithAssumptionsStatus(
            coreAssumptions, kPredecessorCoreConflictLimit);
        coreBlockedInTargetContext =
            coreContextStatus == SATSolverWrapper::SolveStatus::Unsat;
        coreContextResourceLimited =
            coreContextStatus == SATSolverWrapper::SolveStatus::Unknown;
      }
    }
  }
  if (!coreBlockedInTargetContext) {
    if (pdrStatsEnabled() &&
        targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=context_core_sat target=",
          targetCube.size(),
          "->",
          core.size(),
          " source_level=",
          sourceLevel,
          " resource_limit=",
          coreContextResourceLimited ? "true" : "false",
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " context_checks=",
          contextMinimizationChecks);
    }
    return std::nullopt;
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
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core),
          " validation=target_context",
          " context_checks=",
          contextMinimizationChecks);
    }
    return core;
  }

  if (findPredecessorCube(
          problem,
          solverType,
          transitionByState,
          initFormula,
          frameInvariant,
          frames,
          sourceLevel,
          core,
          excludeCurrentTargetForCore,
          complementPartners,
          predecessorProjectionLimit,
          exactFrameClauses,
          resetFrontierCache,
          nullptr,
          predecessorQueryBudget,
          useExactResetFrontierChecks)
          .has_value()) {
    if (pdrStatsEnabled() && targetCube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      emitSecDiag(
          "SEC PDR stats: predecessor core miss reason=predecessor_exists target=",
          targetCube.size(),
          "->",
          core.size(),
          " source_level=",
          sourceLevel,
          " target_hash=",
          cubeFingerprint(targetCube),
          " core_hash=",
          cubeFingerprint(core));
    }
    return std::nullopt;
  }

  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: predecessor core target=",
        targetCube.size(),
        "->",
        core.size(),
        " source_level=",
        sourceLevel,
        " target_hash=",
        cubeFingerprint(targetCube),
        " core_hash=",
        cubeFingerprint(core));
  }
  return core;
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
                                const ComplementPartnerIndex& complementPartners,
                                size_t predecessorProjectionLimit,
                                bool exactFrameClauses,
                                bool useExactResetFrontierChecks,
                                size_t* predecessorQueryBudget) {
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
      !cheapTransitionSurface &&
      (cube.size() > kLargeBlockedCubeGeneralizationThreshold ||
       (cube.size() >= kMinMediumCubePredecessorCoreTargetSize &&
        blockedCubeSupportSize > kMaxGeneralizedBlockedCubeTransitionSupport));
  if (level == 1 && resetFrontierCache != nullptr &&
      problem.resetBootstrapCycles != 0) {
    // A failed exact reset-frontier predecessor precheck already proved that
    // this F1 target has no concrete post-reset predecessor. Reuse the
    // CaDiCaL failed-assumption core recorded by that check before the generic
    // broad-support guard falls back to learning the whole cube verbatim.
    if (const auto resetCore =
            findPdrResetUnreachableCoreForCube(*resetFrontierCache, cube, 1);
        resetCore.has_value() && resetCore->size() < cube.size()) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: reset-predecessor core ",
            "cube=", cube.size(),
            "->", resetCore->size(),
            " level=", level,
            " support=", blockedCubeSupportSize,
            " hash=", cubeFingerprint(*resetCore));
      }
      return *resetCore;
    }
  }
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
            frames,
            level - 1,
            cube,
            resetFrontierCache,
            complementPartners,
            predecessorProjectionLimit,
            exactFrameClauses,
            useExactResetFrontierChecks,
            predecessorQueryBudget);
        core.has_value()) {
      return *core;
    }
  }
  if (!cheapTransitionSurface &&
      cube.size() > kVeryLargeBlockedCubeGeneralizationBypassThreshold) {
    if (level != 1) {
      // Keep the measured benefit of the assumption-core pass above:
      // BlackParrot wide level-1 blockers often collapse from ~100 state bits
      // to a few literals.  If no validated core is available at higher
      // levels, skip slower chunk-dropping probes and learn the already-proven
      // cube verbatim.
      return cube;
    }
  }
  if (!cheapTransitionSurface &&
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
      return false;
    }
    if (!blocksFromInitialFrame &&
        cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      return false;
    }
    return !findPredecessorCube(
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
                nullptr,
                predecessorQueryBudget,
                useExactResetFrontierChecks)
                .has_value();
  };

  StateCube candidate = cube;
  if (cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
    // Large SAT-model cubes often contain a few cheap literals that already
    // explain the blocked transition plus hundreds of unrelated support bits.
    // Try that cheap seed first so generalization does not spend its budget on
    // giant intermediate cubes whose transition cones dominate runtime.
    const StateCube cheapSeed = boundedCheapTransitionCube(
        cube, kLargeBlockedCubeSeedSize, transitionByState);
    if (cheapSeed.size() < cube.size() && checks < checkLimit) {
      ++checks;
      if (reductionStillBlocks(cheapSeed)) {
        candidate = cheapSeed;
      }
    }
    // On ASIC SEC slices, the predecessor query itself is usually the
    // expensive part. Once a large cube is known blockable, spending dozens
    // more predecessor SAT calls to shave a few extra literals often costs more
    // than the smaller clause saves later. The exception is a measured cheap
    // transition surface: then the extra checks cost little and prevent PDR
    // from enumerating thousands of adjacent trivially unreachable cubes.
    if (!cheapTransitionSurface) {
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
}

bool framesConverged(const FrameClauses& lhs, const FrameClauses& rhs) {
  if (lhs.clauses.size() != rhs.clauses.size()) {
    return false;
  }
  for (const auto& clause : lhs.clauses) {
    if (!frameHasSubsumingClause(rhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  for (const auto& clause : rhs.clauses) {
    if (!frameHasSubsumingClause(lhs, clause)) {
      return false;  // LCOV_EXCL_LINE
    }
  }
  return true;
}

bool obligationAlreadyBlocked(const std::vector<FrameClauses>& frames,
                              const ProofObligation& obligation) {
  return frameHasSubsumingClause(frames[obligation.level], clauseFromCube(obligation.cube));
}  // LCOV_EXCL_LINE

BoolExpr* boundedResetReachabilityFrameInvariant(BoolExpr* frameInvariant) {
  if (frameInvariant == nullptr) {
    return nullptr;
  }
  if (frameInvariant->getSupportVars().size() >
      kMaxResetReachabilityFrameInvariantSupport) {
    return nullptr;
  }
  return frameInvariant;
}

ResetFrontierReachabilityContext& resetReachabilityContextFor(
    ResetFrontierCache& cache,
    const KInductionProblem& problem,
    const TransitionExprResolver& transitionByState,
    BoolExpr* frameInvariant) {
  frameInvariant = boundedResetReachabilityFrameInvariant(frameInvariant);
  if (cache.reachabilityContext == nullptr ||
      cache.reachabilityFrameInvariant != frameInvariant) {
    // The optional invariant changes the SAT formula for reset-frontier
    // reachability. Rebuild the immutable context and drop cached SAT answers
    // when switching between invariant-strengthened and plain checks.
    cache.reachabilityContext =
        makeResetFrontierReachabilityContext(
            problem, transitionByState, frameInvariant);
    cache.reachabilityFrameInvariant = frameInvariant;
    cache.outsideByCubeKey.clear();
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
  rememberPdrResetUnreachableCore(
      cache,
      core.has_value() ? cubeFromAssignments(*core) : cube,
      postBootstrapSteps);
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
    bool resourceLimitStartupExactQuery) {
  if (problem.resetBootstrapCycles == 0) {
    return false;
  }
  const std::string key = resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return it->second;
  }
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);
    return true;
  }

  bool outside = false;
  bool outsideFromExactResetFrontier = false;
  const auto knownInitIntersection =
      postBootstrapSteps == 0
          ? cubeIntersectsKnownInitFacts(problem, cube)
          : std::optional<bool>{};
  if (knownInitIntersection.has_value() && !*knownInitIntersection) {
    // Structured init/bootstrap facts are exact facts about the reset frontier.
    // If they already contradict the cube, avoid rebuilding the much heavier
    // reset-prefix SAT query just to rediscover that contradiction.
    outside = true;
  } else if (postBootstrapSteps == 0 &&
      useResetConstantShortcut &&
      (cubeContradictsResetSpecializedConstants(problem, transitionByState, cube) ||
       resetSpecializedConflictCube(
           problem, transitionByState, cache, cube).has_value())) {
    outside = true;
  } else {
    if (postBootstrapSteps == 0 && pdrResetShortcutDiagEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-specialized exact fallback ",
          "cube=",
          cube.size(),
          " use_shortcut=",
          useResetConstantShortcut ? "true" : "false",
          " known_init=",
          knownInitIntersection.has_value()
              ? (*knownInitIntersection ? "sat" : "unsat")
              : "unknown",
          " hash=",
          cubeFingerprint(cube));
    }
    ResetFrontierReachabilityContext& reachabilityContext =
        resetReachabilityContextFor(
            cache, problem, transitionByState, frameInvariant);
    outside =
        mode == ConcreteCubeReachabilityMode::OneShotUnitClauses
            ? !isStateCubeReachableAtResetFrontierOneShot(
                  reachabilityContext,
                  solverType,
                  cubeAssignments(cube),
                  postBootstrapSteps)
            : !isStateCubeReachableAtResetFrontier(
                  reachabilityContext,
                  solverType,
                  cubeAssignments(cube),
                  postBootstrapSteps,
                  /*usePostBootstrapPrechecks=*/true,
                  resourceLimitStartupExactQuery
                      ? kOptionalStartupResetFrontierConflictLimit
                      : -1,
                  resourceLimitStartupExactQuery
                      ? kOptionalStartupResetFrontierPropagationLimit
                      : -1);
    outsideFromExactResetFrontier = outside;
  }
  if (outside) {
    if (outsideFromExactResetFrontier) {
      rememberExactResetFrontierUnreachableCore(
          problem,
          solverType,
          transitionByState,
          cube,
          postBootstrapSteps,
          cache,
          frameInvariant);
    } else {
      rememberPdrAndResetFrontierUnreachableCore(
          cache,
          problem,
          transitionByState,
          cube,
          postBootstrapSteps,
          frameInvariant);
    }
  }
  cache.outsideByCubeKey.emplace(std::move(key), outside);
  return outside;
}

bool cubeOutsideConcreteFrameByCheapResetFacts(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t postBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (problem.resetBootstrapCycles == 0) {
    return false;
  }
  const std::string key = resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return it->second;
  }
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);
    return true;
  }

  std::optional<StateCube> conflict;
  if (postBootstrapSteps == 0) {
    const auto knownInitIntersection =
        cubeIntersectsKnownInitFacts(problem, cube);
    if (knownInitIntersection.has_value() && !*knownInitIntersection) {
      conflict = cube;
    } else if (cubeContradictsResetSpecializedConstants(
                   problem, transitionByState, cube)) {
      conflict = cube;
    } else {
      conflict =
          resetSpecializedConflictCube(problem, transitionByState, cache, cube);
    }
  } else {
    if (const auto transitionImpossibleCore =
            proveTransitionImpossibleResetCoreForCube(
                problem, solverType, transitionByState, cube, cache);
        transitionImpossibleCore.has_value()) {
      conflict = *transitionImpossibleCore;
    } else if (const auto previousCore =
                   findPreviousResetCoreImpliedByOneStepTransition(
                       problem,
                       solverType,
                       transitionByState,
                       cube,
                       postBootstrapSteps,
                       cache);
               previousCore.has_value()) {
      conflict = cube;
    } else {
      const size_t targetStep =
          problem.resetBootstrapCycles + postBootstrapSteps;
      if (const auto priorCoreConflict =
              resetSpecializedPriorCoreConflictAtStep(
                  problem,
                  transitionByState,
                  cube,
                  postBootstrapSteps,
                  targetStep,
                  cache,
                  frameInvariant,
                  /*allowDeepSmallCubeRelaxedBudget=*/false);
          priorCoreConflict.has_value()) {
        conflict = *priorCoreConflict;
      } else if (const auto resetConflict =
                     resetSpecializedConflictCubeAtStep(
                         problem,
                         transitionByState,
                         cache,
                         cube,
                         targetStep,
                         frameInvariant,
                         /*allowDeepSmallCubeRelaxedBudget=*/false);
                 resetConflict.has_value()) {
        conflict = *resetConflict;
      }
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
  const std::string key = resetFrontierCacheKey(cube, postBootstrapSteps);
  if (const auto it = cache.outsideByCubeKey.find(key);
      it != cache.outsideByCubeKey.end()) {
    return !it->second;
  }
  if (const auto cachedCore =
          findPdrResetUnreachableCoreForCube(cache, cube, postBootstrapSteps);
      cachedCore.has_value()) {
    cache.outsideByCubeKey.emplace(key, true);
    return false;
  }

  const auto assignments = cubeAssignments(cube);
  if (problem.resetBootstrapCycles != 0) {
    if (postBootstrapSteps > 0) {
      if (const auto transitionImpossibleCore =
              proveTransitionImpossibleResetCoreForCube(
                  problem,
                  solverType,
          transitionByState,
          cube,
          cache);
          transitionImpossibleCore.has_value()) {
        rememberPdrAndResetFrontierUnreachableCore(
            cache,
            problem,
            transitionByState,
            *transitionImpossibleCore,
            postBootstrapSteps,
            frameInvariant);
        cache.outsideByCubeKey.emplace(key, true);
        return false;
      }
    }

    if (const auto previousCore =
            findPreviousResetCoreImpliedByOneStepTransition(
                problem,
                solverType,
                transitionByState,
                cube,
                postBootstrapSteps,
                cache);
        previousCore.has_value()) {
      rememberPdrAndResetFrontierUnreachableCore(
          cache,
          problem,
          transitionByState,
          cube,
          postBootstrapSteps,
          frameInvariant);
      cache.outsideByCubeKey.emplace(key, true);
      return false;
    }

    ResetSymbolicEvaluator& evaluator =
        resetSymbolicEvaluatorFor(cache, problem, transitionByState);
    evaluator.resetBudget();
    const size_t targetStep =
        problem.resetBootstrapCycles + postBootstrapSteps;
    if (const auto priorCoreConflict =
            resetSpecializedPriorCoreConflictAtStep(
                problem,
                transitionByState,
                cube,
                postBootstrapSteps,
                targetStep,
                cache,
                frameInvariant);
        priorCoreConflict.has_value()) {
      rememberPdrAndResetFrontierUnreachableCore(
          cache,
          problem,
          transitionByState,
          *priorCoreConflict,
          postBootstrapSteps,
          frameInvariant);
      cache.outsideByCubeKey.emplace(key, true);
      return false;
    }
    if (const auto conflict =
            resetSpecializedConflictCubeAtStep(
                problem,
                transitionByState,
                cache,
                cube,
                targetStep,
                frameInvariant);
        conflict.has_value()) {
      // This is the same reset-image proof used for F[0] refinement, evaluated
      // at a later post-reset frame.  Missing transitions remain free
      // variables, so a conflict here is a sound concrete-unreachability fact
      // and avoids the wide bounded SAT unroll sampled on AES.
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: reset-specialized concrete-frame conflict ",
            "post_bootstrap_steps=",
            postBootstrapSteps,
            " cube=",
            cube.size(),
            "->",
            conflict->size(),
            " hash=",
            cubeFingerprint(*conflict));
      }
      // The reset-specialized proof is an exact reset-image conflict, just
      // cheaper than opening the bounded reset-frontier SAT query. Feed it into
      // the lightweight PDR reset-core cache so the next post-bootstrap check
      // can reuse the fact without first constructing the broad reset-frontier
      // SAT context sampled on BlackParrot.
      rememberPdrAndResetFrontierUnreachableCore(
          cache,
          problem,
          transitionByState,
          *conflict,
          postBootstrapSteps,
          frameInvariant);
      cache.outsideByCubeKey.emplace(key, true);
      return false;
    }
  }
  ResetFrontierReachabilityContext& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  const bool reachable =
      mode == ConcreteCubeReachabilityMode::OneShotUnitClauses
          ? isStateCubeReachableAtResetFrontierOneShot(
                reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps,
                usePostBootstrapPrechecks)
          : isStateCubeReachableAtResetFrontier(
                reachabilityContext,
                solverType,
                assignments,
                postBootstrapSteps,
                usePostBootstrapPrechecks);
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
  }
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
    return false;
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
              frameInvariant)) {
        everyStepCheaplyOutside = false;
        remainingExactSteps.push_back(step);
        continue;
      }
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: concrete cube reachability step ",
            "step=", step,
            " result=unsat",
            " mode=", concreteCubeReachabilityModeName(mode));
      }
    }
    if (everyStepCheaplyOutside) {
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: concrete cube reachability cheap reset proof ",
            "cube=", cube.size(),
            " max_step=", maxPostBootstrapSteps);
      }
      return false;
    }
    if (remainingExactSteps.size() <=
        kMaxSparseConcreteReachabilityPerFrameChecks) {
      for (const auto step : remainingExactSteps) {
        const bool reachable = cubeReachableAtConcreteFrame(
            problem,
            solverType,
            transitionByState,
            cube,
            step,
            cache,
            ConcreteCubeReachabilityMode::OneShotUnitClauses,
            frameInvariant);
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: concrete cube reachability sparse step ",
              "step=", step,
              " result=", reachable ? "sat" : "unsat",
              " mode=", concreteCubeReachabilityModeName(
                  ConcreteCubeReachabilityMode::OneShotUnitClauses));
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
      !preferPerFrameValidation) {
    ResetFrontierReachabilityContext& reachabilityContext =
        resetReachabilityContextFor(
            cache, problem, transitionByState, frameInvariant);
    const bool reachable = isStateCubeReachableWithinResetFrontier(
        reachabilityContext,
        solverType,
        cubeAssignments(cube),
        maxPostBootstrapSteps);
    if (!reachable) {
      const auto assignments = cubeAssignments(cube);
      for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
        cache.outsideByCubeKey.emplace(resetFrontierCacheKey(cube, step), true);
        const auto core = SEC::findResetFrontierUnreachableCubeCore(
            reachabilityContext, solverType, assignments, step);
        rememberPdrAndResetFrontierUnreachableCore(
            cache,
            problem,
            transitionByState,
            core.has_value() ? cubeFromAssignments(*core) : cube,
            step,
            frameInvariant);
      }
    }
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: concrete cube reachability shared-prefix ",
          "max_step=", maxPostBootstrapSteps,
          " result=", reachable ? "sat" : "unsat");
    }
    return reachable;
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
  }
  return false;
}

std::optional<StateCube> boundedResetFrontierCoreWithinConcreteFrames(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  if (problem.resetBootstrapCycles == 0 ||
      maxPostBootstrapSteps < kSharedPrefixConcreteValidationMinDepth) {
    return std::nullopt;
  }

  ResetFrontierReachabilityContext& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  const auto assignments = cubeAssignments(cube);
  StateCube unionCore;
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const auto core = findResetFrontierUnreachableCubeCore(
        reachabilityContext,
        solverType,
        assignments,
        step);
    if (!core.has_value()) {
      return std::nullopt;
    }
    for (const auto& [symbol, value] : *core) {
      unionCore.push_back({symbol, value});
    }
  }
  normalizeCube(unionCore);
  if (unionCore.empty() || unionCore.size() >= cube.size()) {
    return std::nullopt;
  }

  // Each per-frame failed-assumption core proves that core unreachable only at
  // its own frame. Their union is stronger than every per-frame core, so it is
  // unreachable at all frames; this final cached check records that fact in the
  // PDR reset cache and guards against backends that return non-core fallbacks.
  if (cubeReachableWithinConcreteFrames(
          problem,
          solverType,
          transitionByState,
          unionCore,
          maxPostBootstrapSteps,
          cache,
          ConcreteCubeReachabilityMode::CachedAssumptions,
          frameInvariant)) {
    return std::nullopt;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: bounded reset-frontier core ",
        "cube=", cube.size(),
        "->", unionCore.size(),
        " max_step=", maxPostBootstrapSteps,
        " hash=", cubeFingerprint(unionCore));
  }
  return unionCore;
}

std::optional<StateCube> cachedResetCoreWithinConcreteFrames(
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    const ResetFrontierCache& cache) {
  StateCube unionCore;
  for (size_t step = 0; step <= maxPostBootstrapSteps; ++step) {
    const auto core =
        findPdrResetUnreachableCoreForCube(cache, cube, step);
    if (!core.has_value()) {
      return std::nullopt;
    }
    unionCore.insert(unionCore.end(), core->begin(), core->end());
  }
  normalizeCube(unionCore);
  if (unionCore.empty() || unionCore.size() >= cube.size()) {
    return std::nullopt;
  }
  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: cached bounded reset core ",
        "cube=", cube.size(),
        "->", unionCore.size(),
        " max_step=", maxPostBootstrapSteps,
        " hash=", cubeFingerprint(unionCore));
  }
  return unionCore;
}

StateCube generalizeResetFrontierCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant) {
  // This is an exact, reset-specific literal dropping pass. A reduced cube is
  // accepted only when the concrete reset-frontier SAT query proves that no
  // real post-reset state can satisfy it. The resulting F[0] clause is thus a
  // stronger abstraction refinement, not a heuristic shortcut.
  StateCube candidate = cube;
  ResetFrontierReachabilityContext& reachabilityContext =
      resetReachabilityContextFor(
          cache, problem, transitionByState, frameInvariant);
  if (const auto core = findResetFrontierUnreachableCubeCore(
          reachabilityContext,
          solverType,
          cubeAssignments(candidate),
          0);
      core.has_value() && core->size() < candidate.size()) {
    candidate = cubeFromAssignments(*core);
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: reset-frontier core ",
          "cube=", cube.size(),
          "->", candidate.size(),
          " hash=", cubeFingerprint(candidate));
    }
    // The failed-assumption core is already an exact unreachable reset-frontier
    // cube.  Do not spend additional SAT calls trying to minimize it further:
    // on AES this optional 2->1 literal probing rebuilt the same 956-symbol
    // reset solver and dominated the PDR regression.
    return candidate;
  }
  size_t index = 0;
  size_t attempts = 0;
  while (index < candidate.size() &&
         attempts < kMaxResetFrontierGeneralizationAttempts) {
    ++attempts;
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (cubeOutsideConcreteResetFrontier(
            problem,
            solverType,
            transitionByState,
            reduced,
            0,
            cache,
            true,
            ConcreteCubeReachabilityMode::CachedAssumptions,
            frameInvariant,
            /*resourceLimitStartupExactQuery=*/true)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

StateCube generalizeInitExcludedCube(const KInductionProblem& problem,
                                     KEPLER_FORMAL::Config::SolverType solverType,
                                     BoolExpr* initFormula,
                                     const StateCube& cube) {
  // Ordinary Init can also be a relational frontier made of equality facts.
  // When a projected predecessor violates that frontier, learn a generalized
  // F[0] clause immediately instead of relying on many small seed clauses to
  // rediscover adjacent impossible cubes one at a time.
  StateCube candidate = cube;
  size_t index = 0;
  size_t attempts = 0;
  while (index < candidate.size() &&
         attempts < kMaxResetFrontierGeneralizationAttempts) {
    ++attempts;
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    if (!cubeIntersectsInit(problem, solverType, initFormula, reduced)) {
      candidate = std::move(reduced);
      continue;
    }
    ++index;
  }
  return candidate;
}

StateCube generalizeBoundedUnreachableRootCube(
    const KInductionProblem& problem,
    KEPLER_FORMAL::Config::SolverType solverType,
    const TransitionExprResolver& transitionByState,
    const StateCube& cube,
    size_t maxPostBootstrapSteps,
    ResetFrontierCache& cache,
    BoolExpr* frameInvariant,
    size_t maxAttempts,
    size_t& attempts) {
  // Every literal drop is checked against the concrete bounded transition
  // prefix, so the learned clause remains a real CEGAR refinement of the
  // projected PDR trace rather than a heuristic pruning trick.
  StateCube candidate = cube;
  if (const auto cachedCore =
          cachedResetCoreWithinConcreteFrames(
              cube, maxPostBootstrapSteps, cache);
      cachedCore.has_value()) {
    attempts = 0;
    return *cachedCore;
  }
  if (maxPostBootstrapSteps > kMaxDepthForBoundedRootGeneralization &&
      transitionByState.stateSymbols().size() >=
          kMinStateSymbolsForDeepRootGeneralizationBypass) {
    attempts = 0;
    return candidate;
  }
  if (const auto resetCore = boundedResetFrontierCoreWithinConcreteFrames(
          problem,
          solverType,
          transitionByState,
          cube,
          maxPostBootstrapSteps,
          cache,
          frameInvariant);
      resetCore.has_value()) {
    attempts = 0;
    return *resetCore;
  }
  size_t index = 0;
  attempts = 0;
  while (index < candidate.size() && attempts < maxAttempts) {
    StateCube reduced = candidate;
    reduced.erase(reduced.begin() + static_cast<std::ptrdiff_t>(index));
    ++attempts;
    const bool preferShallowPerFrameValidation =
        maxPostBootstrapSteps <= kMaxPerFrameConcreteValidationDepth &&
        reduced.size() <= kMaxPerFrameConcreteValidationCubeLiterals;
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

size_t popNextObligationIndex(const std::vector<ProofObligation>& queue) {
  size_t bestIndex = 0;
  for (size_t i = 1; i < queue.size(); ++i) {
    if (queue[i].level < queue[bestIndex].level ||
        (queue[i].level == queue[bestIndex].level &&
         (queue[i].cube.size() < queue[bestIndex].cube.size() ||
          (queue[i].cube.size() == queue[bestIndex].cube.size() &&
           queue[i].badFrame < queue[bestIndex].badFrame)))) {
      bestIndex = i;
    }
  }
  return bestIndex;
}

std::string proofObligationKey(const ProofObligation& obligation) {
  std::string key;
  key.reserve(32 + obligation.cube.size() * 24);
  key.append(std::to_string(obligation.level));
  key.push_back('|');
  key.append(std::to_string(obligation.badFrame));
  for (const auto& literal : obligation.cube) {
    key.push_back('|');
    key.append(std::to_string(literal.symbol));
    key.push_back('=');
    key.push_back(literal.value ? '1' : '0');
  }
  key.append("|root");
  for (const auto& literal : obligation.rootCube) {
    key.push_back('|');
    key.append(std::to_string(literal.symbol));
    key.push_back('=');
    key.push_back(literal.value ? '1' : '0');
  }
  return key;
}

void enqueueProofObligation(std::vector<ProofObligation>& queue,
                            std::unordered_set<std::string>& queuedKeys,
                            ProofObligation obligation) {
  // Large SEC output cones can reach the same normalized cube/level pair
  // through several predecessor projections before a learned frame clause
  // subsumes it. Keep only one pending copy: once that obligation is blocked
  // or reaches Init, every duplicate would repeat the same SAT work.
  const std::string key = proofObligationKey(obligation);
  if (!queuedKeys.insert(key).second) {
    return;
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
                           const StateCube& rootCube,
                           size_t rootLevel,
                           size_t& badFrame,
                           const ComplementPartnerIndex& complementPartners,
                           size_t predecessorProjectionLimit,
                           bool exactFrameClauses,
                           bool refineProjectedCounterexamples,
                           ResetFrontierCache& resetFrontierCache,
                           size_t maxBoundedRootGeneralizationAttempts,
                           bool learnValidatedBadFormulaClausesOnReject,
                           bool useExactResetFrontierChecks,
                           size_t* predecessorQueryBudget) {
  // This is the paper's recursive blocking idea expressed as an explicit queue
  // so we do not depend on deep recursion for large obligation stacks.
  std::vector<ProofObligation> queue;
  std::unordered_set<std::string> queuedKeys;
  enqueueProofObligation(
      queue, queuedKeys, ProofObligation{rootCube, rootLevel, rootLevel, rootCube});
  bool expandedBadFormulaObligations = false;
  if (learnValidatedBadFormulaClausesOnReject &&
      problem.observedOutputExprs0.size() == 1 &&
      rootLevel > 0) {
    auto badClauses = observedOutputBadFormulaClauses(
        problem, transitionByState.stateSymbols());
    if (!badClauses.has_value()) {
      badClauses =
          stateOnlyBadFormulaClauses(problem.bad, transitionByState.stateSymbols());
    }
    if (badClauses.has_value() &&
        badClauses->size() > kMaxExactValidatedBadFormulaClauses &&
        badClauses->size() <= kMaxSingleOutputExactValidatedBadFormulaClauses) {
      size_t seededObligations = 0;
      for (const auto& clause : *badClauses) {
        const StateCube badCube = cubeForbiddenByStateClause(clause);
        enqueueProofObligation(
            queue,
            queuedKeys,
            ProofObligation{badCube, rootLevel, rootLevel, badCube});
        ++seededObligations;
      }
      expandedBadFormulaObligations = seededObligations != 0;
      if (expandedBadFormulaObligations && pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: expanded state-only bad formula into "
            "PDR obligations ",
            "bad_frame=", rootLevel,
            " obligations=", seededObligations);
      }
    }
  }
  const InitFactIndex initFacts = buildInitFactIndex(problem);
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
        complementPartners,
        predecessorProjectionLimit,
        exactClausesForGeneralization,
        useExactResetFrontierChecks,
        predecessorQueryBudget);
    addClauseToFrames(
        frames, clauseFromCube(generalizedCube), blockedObligation.level);
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
    }
  };
  auto learnBlockedObligationVerbatim =
      [&](const ProofObligation& blockedObligation) {
    // The projected-frame CEGAR loop below can prove a cube blocked only after
    // adding a few missing learned-frame clauses to that local query. Those
    // clauses are real frame facts, so learning the original cube is sound; we
    // intentionally skip optional literal-dropping here because re-running
    // generalization without the same local CEGAR blockers can rediscover the
    // stale predecessor that we just eliminated.
    addClauseToFrames(
        frames, clauseFromCube(blockedObligation.cube), blockedObligation.level);
    if (blockedObligation.level < blockedObligation.badFrame) {
      enqueueProofObligation(
          queue,
          queuedKeys,
          ProofObligation{
              blockedObligation.cube,
              blockedObligation.level + 1,
              blockedObligation.badFrame,
              blockedObligation.rootCube});
      }
  };
  // Validated bad-formula learning is an exact repair for final SEC leaves:
  // concrete BMC validates the bad predicate and learns its state-only CNF.
  // Keep it eager for small state surfaces, and also for already-split
  // single-output leaves. AES samples showed those leaves otherwise spend
  // minutes proving a tiny root cube through the broad reset image, while the
  // bad-formula validator uses the localized proof-only base-case profile.
  const bool usePredecessorResetFrontierChecks =
      useExactResetFrontierChecks;
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
      expandedBadFormulaObligations;
  const bool useRootResetFrontierChecks =
      useExactResetFrontierChecks && predecessorProjectionLimit != 0 &&
      !skipRootResetFrontierForBadFormulaRepair;
  const bool useCheapRootResetFrontierFacts =
      refineProjectedCounterexamples && problem.resetBootstrapCycles != 0;

  const bool useSingleOutputValidatedBadFormulaRepair =
      learnValidatedBadFormulaClausesOnReject &&
      problem.observedOutputExprs0.size() == 1;
  const bool useWholeBatchValidatedBadFormulaRepair =
      learnValidatedBadFormulaClausesOnReject &&
      exactFrameClauses &&
      problem.observedOutputExprs0.size() > 1;
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
       transitionByState.stateSymbols().size() <=
           kMaxDeepEagerBadFormulaStateSymbols);
  const bool allowEagerBadFormulaValidationAtRoot =
      problem.resetBootstrapCycles == 0 ||
      rootLevel == 1 ||
      expandedBadFormulaObligations ||
      useWholeBatchValidatedBadFormulaRepair ||
      usePerOutputValidatedBadFormulaRepair;
  if (refineProjectedCounterexamples &&
      problem.observedOutputExprs0.size() > 1 &&
      !usePerOutputValidatedBadFormulaRepair &&
      !useWholeBatchValidatedBadFormulaRepair &&
      rootLevel > kMaxMultiOutputProjectedRootValidationFrame &&
      transitionByState.stateSymbols().size() >=
          kMinStateSymbolsForDeepRootGeneralizationBypass) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: deferred multi-output root bad-formula repair ",
          "bad_frame=", rootLevel,
          " outputs=", problem.observedOutputExprs0.size(),
          " root_cube=", rootCube.size());
    }
    badFrame = rootLevel;
    return false;
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
  }

  while (!queue.empty()) {
    const size_t obligationIndex = popNextObligationIndex(queue);
    const ProofObligation obligation = queue[obligationIndex];
    queuedKeys.erase(proofObligationKey(obligation));
    queue.erase(queue.begin() + static_cast<std::ptrdiff_t>(obligationIndex));
    const bool obligationExactFrameClauses = exactFrameClauses;

    if (obligationAlreadyBlocked(frames, obligation)) {
      continue;
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
        // bad-formula repair below, so this path should stay a narrow F[0]
        // refinement and not become the only way we learn repeated output-bad
        // assignments.
        const StateCube generalizedCube = generalizeResetFrontierCube(
            problem,
            solverType,
            transitionByState,
            obligation.cube,
            resetFrontierCache,
            frameInvariant);
        addClauseToFrame(
            frames[0],
            clauseFromCube(generalizedCube));
        continue;
      }
      if (const auto conflictCube =
              knownInitConflictCube(initFacts, obligation.cube);
          conflictCube.has_value()) {
        // Ordinary relational Init has the same refinement opportunity as the
        // reset-frontier path.  When the cube visibly contradicts a structured
        // init fact, learn only that conflict instead of a wide SAT-model cube;
        // this keeps large ASIC output slices from rediscovering the same
        // state equality violation thousands of times.
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: known init conflict ",
              "cube=", obligation.cube.size(),
              " core=", conflictCube->size(),
              " bad_frame=", obligation.badFrame,
              " hash=", cubeFingerprint(*conflictCube));
        }
        addClauseToFrame(frames[0], clauseFromCube(*conflictCube));
        continue;
      }
      if (!cubeIntersectsInit(problem, solverType, initFormula, obligation.cube)) {
        const StateCube generalizedCube = generalizeInitExcludedCube(
            problem,
            solverType,
            initFormula,
            obligation.cube);
        addClauseToFrame(frames[0], clauseFromCube(generalizedCube));
        continue;
      }
      if (pdrStatsEnabled()) {
        emitSecDiag(
            "SEC PDR stats: counterexample candidate reached init ",
            "bad_frame=", obligation.badFrame,
            " cube=", obligation.cube.size(),
            " root_cube=", obligation.rootCube.size());
      }
      if (!refineProjectedCounterexamples) {
        // SEC strategy runs a concrete base-case validation immediately after
        // every PDR difference. Projected retry stages therefore do not need to
        // spend another exact bounded-prefix query here; returning the
        // candidate lets the caller either accept a real witness or move to the
        // next precision stage.
        badFrame = obligation.badFrame;
        return false;
      }
      if (problem.observedOutputExprs0.size() > 1 &&
          !usePerOutputValidatedBadFormulaRepair &&
          !useWholeBatchValidatedBadFormulaRepair &&
          obligation.badFrame >
              kMaxMultiOutputProjectedRootValidationFrame) {
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: deferred deep multi-output root validation ",
              "bad_frame=", obligation.badFrame,
              " outputs=", problem.observedOutputExprs0.size(),
              " root_cube=", obligation.rootCube.size());
        }
        badFrame = obligation.badFrame;
        return false;
      }
      const bool allowEagerBadFormulaValidationForReject =
          problem.resetBootstrapCycles == 0 ||
          obligation.badFrame == 1 ||
          expandedBadFormulaObligations ||
          useWholeBatchValidatedBadFormulaRepair ||
          usePerOutputValidatedBadFormulaRepair;
      if (learnValidatedBadFormulaClausesOnReject &&
          useEagerBadFormulaValidation &&
          allowEagerBadFormulaValidationForReject) {
        const auto refinement = learnValidatedBadFormulaClauses(
              problem,
              solverType,
              transitionByState,
              frameInvariant,
              frames,
              obligation.badFrame,
              badFrame,
              resetFrontierCache,
              useWholeBatchValidatedBadFormulaRepair);
        if (refinement.has_value()) {
          return *refinement;
        }
      }
      const StateCube& concreteTarget =
          obligation.rootCube.empty() ? obligation.cube : obligation.rootCube;
      const bool preferShallowPerFrameValidation =
          obligation.badFrame <= kMaxPerFrameConcreteValidationDepth &&
          concreteTarget.size() <= kMaxPerFrameConcreteValidationCubeLiterals;
      const ConcreteCubeReachabilityMode concreteValidationMode =
          !preferShallowPerFrameValidation &&
                  obligation.badFrame >= kCachedConcreteValidationMinDepth &&
                  concreteTarget.size() >=
                      kCachedConcreteValidationMinCubeLiterals
              ? ConcreteCubeReachabilityMode::CachedAssumptions
              : ConcreteCubeReachabilityMode::OneShotUnitClauses;
      if (!cubeReachableWithinConcreteFrames(
              problem,
              solverType,
              transitionByState,
              concreteTarget,
              obligation.badFrame,
              resetFrontierCache,
              concreteValidationMode,
              frameInvariant)) {
        // Projected predecessor cubes can be reachable even when the original
        // bad/frontier cube they came from is not.  Before accepting such a
        // path as a counterexample, validate the root cube with the exact
        // bounded transition prefix. If no concrete prefix reaches it, learn a
        // bounded-safe frame clause and keep the ordinary PDR loop going.
        size_t generalizationAttempts = 0;
        const StateCube generalizedTarget =
            generalizeBoundedUnreachableRootCube(
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
          addClauseToFrame(frames[0], refinedClause);
        } else {
          addClauseToFrames(frames, refinedClause, obligation.badFrame);
        }
        if (pdrStatsEnabled()) {
          emitSecDiag(
              "SEC PDR stats: refined projected counterexample ",
              "bad_frame=", obligation.badFrame,
              " root_cube=", concreteTarget.size(),
              "->", generalizedTarget.size(),
              " checks=", generalizationAttempts);
        }
        if (learnValidatedBadFormulaClausesOnReject &&
            useSingleOutputValidatedBadFormulaRepair) {
          // The concrete root check records reset-unreachable cores for every
          // frame it proves. Immediately give the state-only bad-formula
          // repair a chance to consume those cached exact cores, otherwise PDR
          // can rediscover neighboring bad assignments one at a time.
          (void)learnValidatedBadFormulaClauses(
              problem,
              solverType,
              transitionByState,
              frameInvariant,
              frames,
              obligation.badFrame,
              badFrame,
              resetFrontierCache);
        }
        return true;
      }
      badFrame = obligation.badFrame;
      return false;
    }

    const size_t obligationProjectionLimit =
        predecessorProjectionLimitForObligation(
            obligation.level, predecessorProjectionLimit);

    if (obligation.cube.size() > kLargeBlockedCubeGeneralizationThreshold) {
      // For a large target cube, first try to block a cheap subset.  If no
      // predecessor can reach the subset, then no predecessor can reach the
      // stronger original cube either, and we avoid building a SAT query for a
      // thousand next-state functions just to learn the same small clause.
      const StateCube cheapTarget = boundedCheapTransitionCube(
          obligation.cube, kLargeBlockedCubeSeedSize, transitionByState);
      if (cheapTarget.size() < obligation.cube.size() &&
          !findPredecessorCube(
               problem,
               solverType,
               transitionByState,
               initFormula,
               frameInvariant,
               frames,
               obligation.level - 1,
               cheapTarget,
               false,
               complementPartners,
               obligationProjectionLimit,
               obligationExactFrameClauses,
               &resetFrontierCache,
               nullptr,
               predecessorQueryBudget,
               usePredecessorResetFrontierChecks)
               .has_value()) {
        const StateCube generalizedCube = generalizeBlockedCube(
            problem,
            solverType,
            transitionByState,
            initFormula,
            frameInvariant,
            frames,
            obligation.level,
            cheapTarget,
            &resetFrontierCache,
            complementPartners,
            obligationProjectionLimit,
            obligationExactFrameClauses,
            usePredecessorResetFrontierChecks,
            predecessorQueryBudget);
        addClauseToFrames(frames, clauseFromCube(generalizedCube), obligation.level);
        if (obligation.level < obligation.badFrame) {
          const StateCube propagatedRoot =
              obligation.rootCube.empty() ? generalizedCube : obligation.rootCube;
          enqueueProofObligation(
              queue,
              queuedKeys,
              ProofObligation{
                  generalizedCube,
                  obligation.level + 1,
                  obligation.badFrame,
                  propagatedRoot});
        }
        continue;
      }
    }

    std::vector<StateClause> projectedFrameRefinements;
    std::unordered_set<std::string> projectedFrameRefinementKeys;
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
          projectedFrameRefinements.empty() ? nullptr : &projectedFrameRefinements,
          predecessorQueryBudget,
          usePredecessorResetFrontierChecks);
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
                    frames[predecessorObligation.level], predecessorClause)
              : std::optional<StateClause>{};
      if (blockingClause.has_value()) {
        // Projected frame encoding is sound but incomplete: it may omit the
        // learned clause that already blocks this predecessor.  Re-enqueueing
        // such a stale predecessor creates a reset-frontier loop. Refine only
        // this local SAT query with the missing learned blocker instead of
        // rebuilding the query with every clause from the full frame.
        const std::string blockingKey = stateClauseKey(*blockingClause);
        if (projectedFrameRefinementKeys.insert(blockingKey).second) {
          projectedFrameRefinements.push_back(*blockingClause);
          if (pdrStatsEnabled()) {
            const size_t retryNumber = nextPdrProjectedBlockedRetryNumber();
            if (retryNumber <= kInitialPdrStatsQueries ||
                retryNumber % pdrStatsInterval() == 0) {
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
          if (pdrStatsEnabled()) {
            emitSecDiag(
                "SEC PDR stats: projected-frame refinement cap reached ",
                "level=", obligation.level,
                " cube=", obligation.cube.size(),
                " predecessor=", predecessorObligation.cube.size(),
                " refinements=", projectedFrameRefinements.size());
          }
        } else if (pdrStatsEnabled()) {
          // If the same blocker was already added and the projected query still
          // returns a predecessor blocked by it, keep the algorithm
          // conservative: fall back to the exact-frame path once instead of
          // spinning forever.
          emitSecDiag(
              "SEC PDR stats: exact retry for duplicate projected blocker ",
              "level=", obligation.level,
              " cube=", obligation.cube.size(),
              " predecessor=", predecessorObligation.cube.size());
        }
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
            complementPartners,
            obligationProjectionLimit,
            true,
            &resetFrontierCache,
            nullptr,
            predecessorQueryBudget,
            usePredecessorResetFrontierChecks);
        if (!exactPredecessor.has_value()) {
          learnBlockedObligation(obligation, true);
          break;
        }
        const StateCube exactQueuedPredecessor =
            obligation.level == 1
                ? *exactPredecessor
                : boundedPrefixCube(*exactPredecessor, obligationProjectionLimit);
        predecessorObligation = ProofObligation{
            exactQueuedPredecessor,
            obligation.level - 1,
            obligation.badFrame,
            obligation.rootCube};
      }
      enqueueProofObligation(queue, queuedKeys, obligation);
      enqueueProofObligation(queue, queuedKeys, predecessorObligation);
      break;
    }
  }

  return true;
}

std::vector<StateClause> buildSeedClauses(const KInductionProblem& problem) {
  std::vector<StateClause> seedClauses;
  // Seed the first learned frame with state equalities that are already
  // guaranteed by Init/bootstrap, so PDR starts from facts that are known
  // reachable-state invariants instead of rediscovering them from scratch.
  //
  // This deliberately uses only structured init/bootstrap facts. Running an
  // exact SAT init-intersection query for every possible equality seed is too
  // expensive on ASIC regressions and is not needed for soundness: if a seed is
  // not cheaply known to hold on the startup frontier, we simply do not seed it.
  const InitFactIndex initFacts = buildInitFactIndex(problem);
  for (const auto& [lhsSymbol, rhsSymbol] : problem.inductiveStateEqualityPairs) {
    StateClause clause0 = {{lhsSymbol, false}, {rhsSymbol, true}};
    StateClause clause1 = {{lhsSymbol, true}, {rhsSymbol, false}};
    normalizeClause(clause0);
    normalizeClause(clause1);

    // Promote already-anchored state equalities into initial frame facts when
    // they are guaranteed by Init/bootstrap instead of guessed from structure.
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, true, rhsSymbol, false)) {
      seedClauses.push_back(clause0);
    }
    if (twoLiteralCubeIsKnownOutsideInit(
            initFacts, lhsSymbol, false, rhsSymbol, true)) {
      seedClauses.push_back(clause1);
    }
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

BoolExpr* buildStateAndOutputInvariant(
    const KInductionProblem& problem,
    const std::vector<std::pair<size_t, size_t>>& equalityPairs) {
  BoolExpr* invariant = buildStateEqualityInvariant(equalityPairs);
  if (invariant == nullptr) {
    invariant = BoolExpr::createTrue();
  }
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
  symbols.reserve(equalityPairs.size() * 2);
  for (const auto& [lhsSymbol, rhsSymbol] : equalityPairs) {
    symbols.insert(lhsSymbol);
    symbols.insert(rhsSymbol);
  }
  return sortUniqueSymbols(std::move(symbols));
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

  SATSolverWrapper solver(solverType);
  const auto solverSymbols = sortUniqueSymbols(std::move(querySymbols));
  FrameVariableStore variables(solver, solverSymbols, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs0, 2);
  addComplementedStateRelations(solver, variables, problem.complementedStatePairs1, 2);
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
  solver.addClause({nextEncoder.encode(BoolExpr::Not(invariant))});
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
    return std::vector<std::pair<size_t, size_t>>{};
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
      !initialFrontierImplies(initFormula, invariant, solverType)) {
    return nullptr;
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
      }
      if (selectedPairs != nullptr) {
        *selectedPairs = equalityPairs;
      }
      return invariant;
    }
    if (prunedPairs->empty()) {
      break;
    }
    equalityPairs = std::move(*prunedPairs);
  }

  if (pdrStatsEnabled()) {
    emitSecDiag(
        "SEC PDR stats: frame invariant state_equality_subset unavailable ",
        "remaining_pairs=", equalityPairs.size(),
        " iterations=", kMaxStateEqualitySubsetIterations);
  }
  return nullptr;
}

BoolExpr* selectPdrFrameInvariant(const KInductionProblem& problem,
                                  BoolExpr* initFormula,
                                  KEPLER_FORMAL::Config::SolverType solverType) {
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
    return nullptr;
  }

  FormulaSupportCache invariantSupportCache;
  auto validateCandidate = [&](const char* label, BoolExpr* candidate) -> BoolExpr* {
    if (candidate == nullptr) {
      if (pdrStatsEnabled()) {
        emitSecDiag("SEC PDR stats: frame invariant ", label, " unavailable");
      }
      return nullptr;
    }

    const bool initImpliesCandidate =
        initialFrontierImplies(initFormula, candidate, solverType);
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
    // subset.  It still has to pass the same init and one-step inductiveness
    // checks before PDR may use it as a frame fact.
    BoolExpr* sharedStrengthening =
        selectValidatedStrengtheningInvariant(problem, initFormula, solverType);
    return validateCandidate("shared_strengthening", sharedStrengthening);
  };

  if (BoolExpr* stateInvariant =
          validateCandidate("state_equalities", buildStateEqualityInvariant(problem))) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated state-equality frame invariant with ",
          problem.inductiveStateEqualityPairs.size(),
          " equality pairs");
    }
    return stateInvariant;
  }

  std::vector<std::pair<size_t, size_t>> stateSubsetPairs;
  if (BoolExpr* stateSubsetInvariant =
          selectInductiveStateEqualitySubsetInvariant(
              problem, initFormula, solverType, &stateSubsetPairs)) {
    // A state-only subset may be inductive but too weak to exclude the output
    // mismatch, causing PDR to rediscover the output equality as thousands of
    // tiny blocking clauses.  Strengthen that subset with the current output
    // equality only when the combined formula is itself proved valid on Init
    // and inductive across one transition.  The result is still just a PDR
    // frame fact; it is not an external fast proof path.
    if (BoolExpr* outputStrengthenedInvariant =
            validateCandidate(
                "state_equality_subset_outputs",
                buildStateAndOutputInvariant(problem, stateSubsetPairs))) {
      if (isSecDiagEnabled()) {
        emitSecDiag(
            "SEC diag: PDR using validated state/output subset frame invariant");
      }
      return outputStrengthenedInvariant;
    }

    if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
      if (isSecDiagEnabled()) {
        emitSecDiag(
            "SEC diag: PDR using validated SEC strengthening frame invariant");
      }
      return strengthenedInvariant;
    }

    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated state-equality subset frame invariant");
    }
    return stateSubsetInvariant;
  }

  // Some SEC proofs need the full extracted strengthening lemma, not just the
  // raw state-equality core. This is still used as a PDR frame constraint only
  // after the same inductiveness check succeeds.
  if (BoolExpr* strengthenedInvariant = selectSharedStrengthening()) {
    if (isSecDiagEnabled()) {
      emitSecDiag(
          "SEC diag: PDR using validated SEC strengthening frame invariant");
    }
    return strengthenedInvariant;
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
                      size_t* predecessorQueryBudget) {
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
      if (!findPredecessorCube(
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
               nullptr,
               predecessorQueryBudget)
               .has_value()) {
        addClauseToFrame(frames[level + 1], clause);
      }
    }
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
      oss << ", ";
    }
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
      oss << " OR ";
    }
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

  // A reset-bootstrap frontier may be summarized by only the state facts the
  // extractor could prove cheaply. Before PDR treats that summary as F[0], run
  // the concrete one-shot reset BMC used by the other SEC engines. If it finds
  // a real bad post-reset state, report it; otherwise PDR is allowed to add the
  // checked property as a safe F[0] fact below.
  if (auto witness = findBaseCounterexample(problem, solverType, 0);
      witness.has_value()) {
    return PDRResult{PDRStatus::Different, witness->badFrame};
  }
  resetBootstrapFrameCheckedSafe = true;
  return std::nullopt;
}

BoolExpr* buildPdrInitFormula(const KInductionProblem& problem,
                              bool resetBootstrapFrameCheckedSafe) {
  BoolExpr* initFormula = buildProofInitFormula(problem);
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
                     bool useExactResetFrontierChecks)
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
      useExactResetFrontierChecks_(useExactResetFrontierChecks) {}

PDRResult PDREngine::run(size_t maxFrames,
                         bool resetBootstrapFrameCheckedSafe) const {
  // Build the SEC startup frontier once so every frame query shares the same
  // interpretation of reset/bootstrap and frame-0 equality constraints.
  emitPdrTraceProblem(problem_);
  if (const auto resetProof = checkResetBootstrapFrameZero(
          problem_, solverType_, resetBootstrapFrameCheckedSafe);
      resetProof.has_value()) {
    return *resetProof;
  }

  BoolExpr* initFormula =
      buildPdrInitFormula(problem_, resetBootstrapFrameCheckedSafe);
  if (initFormula == nullptr) {
    return {PDRStatus::Inconclusive, 0};
  }

  // PDR still establishes convergence through its own frame/blocking loop, but
  // it may use validated state-correspondence equalities as a frame invariant.
  // Those equalities come from the shared SEC extraction/reset analysis and are
  // checked for init coverage and transition preservation before use.
  BoolExpr* frameInvariant =
      selectPdrFrameInvariant(problem_, initFormula, solverType_);
  const bool exactFrameClauses = useExactFrameClauses_;
  // Bad-state queries decide whether the current frontier still contains a
  // property violation. When SEC/PDR repair learns many tiny reset-conflict
  // blockers, a projected frame view can hide exactly those blockers behind
  // unrelated clauses and make PDR rediscover stale bad cubes. Keep only the
  // bad query exact; predecessor queries below remain projected.
  const bool exactBadQueryFrameClauses =
      exactFrameClauses || learnValidatedBadFormulaClauses_;
  const bool exactPropagationFrameClauses =
      exactFrameClauses || learnValidatedBadFormulaClauses_;

  TransitionExprResolver transitionByState(problem_);
  ComplementPartnerIndex complementPartners(problem_);
  // The bad predicate is the same for every frame query. Cache its state
  // support once so repeated PDR bad-cube checks do not rebuild the large
  // combined miter state set on every loop iteration.
  const auto preciseBadStateSupport = collectBoundedStateSupportSymbols(
      problem_.bad,
      kMaxPreciseBadCubeSupportNodes,
      preciseBadCubeStateLimit_,
      transitionByState.stateSymbols());
  ResetFrontierCache resetFrontierCache;
  size_t remainingPredecessorQueries = maxPredecessorQueries_;
  size_t* predecessorQueryBudget =
      maxPredecessorQueries_ == 0 ? nullptr : &remainingPredecessorQueries;
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
            preciseBadCubeStateLimit_,
            transitionByState.stateSymbols(),
            0,
            complementPartners,
            exactBadQueryFrameClauses);
        badCube.has_value()) {
      emitPdrTrace("bad_cube@F0", formatCubeForPdrTrace(*badCube));
      return {PDRStatus::Different, 0};
    }
  }

  if (maxFrames == 0) {
    return {PDRStatus::Inconclusive, 0};
  }

  const auto seedClauses = buildSeedClauses(problem_);
  frames.emplace_back(FrameClauses{seedClauses});
  emitPdrTraceFrames("seeded_frames", frames);
  try {
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
              preciseBadCubeStateLimit_,
              transitionByState.stateSymbols(),
              level,
              complementPartners,
              exactBadQueryFrameClauses);
      if (!badCube.has_value()) {
        break;
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
              *badCube,
              level,
              badFrame,
              complementPartners,
              predecessorProjectionLimit_,
              exactFrameClauses,
              refineProjectedCounterexamples_,
              resetFrontierCache,
              maxBoundedRootGeneralizationAttempts_,
              learnValidatedBadFormulaClauses_,
              useExactResetFrontierChecks_,
              predecessorQueryBudget)) {
        emitPdrTraceFrames("frames_before_counterexample", frames);
        return {PDRStatus::Different, badFrame};
      }
      emitPdrTraceFrames("frames_after_blocking", frames);
    }

    // Phase 2: create the next frame, seed it with already-known startup
    // facts
    frames.emplace_back(FrameClauses{seedClauses});
    // and then try to push learned clauses forward.
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
        predecessorProjectionLimit_,
        exactPropagationFrameClauses,
        predecessorQueryBudget);
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
  } catch (const PdrQueryBudgetExceeded&) {
    if (pdrStatsEnabled()) {
      emitSecDiag(
          "SEC PDR stats: predecessor query budget exhausted limit=",
          maxPredecessorQueries_);
    }
    return {PDRStatus::Inconclusive, maxFrames};
  }

  return {PDRStatus::Inconclusive, maxFrames};  // LCOV_EXCL_LINE
}

}  // namespace KEPLER_FORMAL::SEC

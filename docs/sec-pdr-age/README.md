# Dual-Rail PDR Age Discovery

This document describes automatic age discovery for SEC runs using the PDR
engine and `dual_rail_steady` encoding. The flow finds a cycle age after which
the selected public outputs of both designs are proved binary-defined. SEC can
then prove concrete output equality without treating a persistent unknown value
as a concrete proof.

The feature is enabled by default in the command-line frontend. Disable it with
`--no-sec-pdr-auto-age` or `sec_pdr_auto_age: false` to use the existing PDR
flow unchanged.

## Scope And Invariants

Automatic age discovery applies only when both of these are selected:

- `--sec-engine pdr`
- `--sec-encoding dual_rail_steady`

The implementation preserves these rules:

- PDR always receives the complete SEC transition system.
- PDR always starts from the exact extracted initial predicate, `F[0] = I`.
- No output, state bit, transition, or initial constraint is removed.
- No relation is created between internal elements of the two designs.
- No internal name matching is used across designs.
- Every age probe starts fresh IC3/PDR frames and proof obligations.
- A solver `UNKNOWN` result is never interpreted as SAT, UNSAT, or coverage.

## Dual-Rail Values

Each encoded value has a `may-be-one` rail and a `may-be-zero` rail:

| Rails | Meaning |
| --- | --- |
| `01` | Binary `0` |
| `10` | Binary `1` |
| `11` | Unknown `X` |
| `00` | Invalid and excluded by the dual-rail state constraints |

For output `o`, binary definedness is:

```text
defined(o) = o.may_be_one XOR o.may_be_zero
```

A concrete mismatch exists only when both designs are defined and their binary
values are opposite.

## Verifier-Owned Age Monitor

The flow adds one deterministic, saturating age counter to the product FSM. The
counter is verifier-owned auxiliary state: it belongs to neither design and
does not relate design state.

- The exact initial predicate sets `age = 0`.
- Each transition increments the counter.
- At the configured maximum, the counter remains at the maximum.
- Values above the maximum are unreachable and transition back to the maximum.

The selected age is a property-monitor threshold. It is not PDR frame `F[N]`
and it does not replace the extracted initial predicate.

## Definedness Property

For an output batch `B` and candidate age `N`, PDR checks the safety property:

```text
age < N OR all outputs in B are binary-defined in both designs
```

An `Equivalent` PDR result is a certificate that every reachable state from age
`N` onward has binary-defined values for that batch. `Different` means the age
is too small. `Inconclusive` means only that PDR did not decide the property
within its resource budget.

## Age Search

The command-line defaults are:

```text
minimum age = 10
maximum age = 20
```

For each output batch, the search is:

1. Prove the definedness property at the configured minimum.
2. If that is not proved, prove it at the configured maximum.
3. If the maximum is proved, use binary search to find the smallest certified
   age between the two bounds.
4. If a binary-search probe is inconclusive, keep the smallest already-proved
   upper age. Never infer a result from `UNKNOWN`.
5. If the maximum is not proved for a multi-output batch, split the batch and
   repeat the search.
6. If the maximum is not proved for a single output, use the fallback flow at
   the configured maximum.

Each age property is monotone: once all selected outputs are proved defined from
age `N`, the same certificate holds for any larger candidate age.

## Final SEC Property

When age `N` is certified, PDR checks the existing guarded mismatch property
starting at that age:

```text
age < N OR no selected output is binary-defined and opposite
```

The definedness certificate and guarded mismatch proof together establish
concrete equality from age `N` onward. A reachable defined-and-opposite output
is reported as `Different`.

Startup behavior before the selected age is intentionally outside this
steady-state property. The age monitor makes that boundary explicit in the
product FSM instead of confusing it with a PDR frame number.

## Uncertified Fallback

If a single output is not certified as defined by the maximum age, SEC retains
the existing two checks, both gated at the maximum age:

1. Guarded binary mismatch checks for a concrete `01` versus `10` difference.
2. Strict rail equality checks whether the two three-valued rail pairs differ.

A guarded binary mismatch is a concrete counterexample. Otherwise, the output
remains `Inconclusive`, even if strict `X == X` rail equality is proved, because
definedness was not certified. The result names every affected public output
and explains that unknown data propagated from uninitialized sequential logic.

## Disabled Flow

With automatic age discovery disabled, the monitor and all age probes are
absent. SEC runs the existing behavior unchanged:

1. Run guarded dual-rail PDR from the original `F[0]` with the requested
   `max_k`.
2. Run the existing strict rail-equality pass for guarded-proved batches.
3. Use the existing batching, output coverage, diagnostics, and verdict rules.

No age gating or effective frame-budget adjustment occurs on this path.

## Reused Work

Age probes share only property-independent model work:

- The exact `F[0]` formula.
- The incremental `F[0]`-intersection SAT solver.
- The incremental `F[0] -> T -> cube` predecessor SAT solver.
- The frame-zero bad-state solver infrastructure.
- Transition expressions, lazy transition support, and Tseitin clauses already
  stored in those shared solvers.
- Prebuilt output-definedness expressions and age-comparison expressions.

The following are deliberately not shared because they depend on the property
or on a specific PDR run:

- PDR frames and learned frame clauses.
- Proof obligations and predecessor results from higher frames.
- Convergence results.
- Counterexamples or `UNKNOWN` verdicts.

This cache boundary affects performance only. Removing the caches must not
change a verdict.

## Configuration

| CLI | YAML | Default | Meaning |
| --- | --- | ---: | --- |
| `--sec-pdr-auto-age` | `sec_pdr_auto_age: true` | enabled | Enable automatic age discovery. |
| `--no-sec-pdr-auto-age` | `sec_pdr_auto_age: false` | enabled | Disable age discovery and preserve the existing PDR flow. |
| `--sec-pdr-age-min N` | `sec_pdr_age_min: N` | `10` | First candidate age. |
| `--sec-pdr-age-max N` | `sec_pdr_age_max: N` | `20` | Last candidate and fallback age. |

Both ages are non-negative integers and the minimum must not exceed the
maximum. Explicit age options are rejected unless PDR and dual-rail steady-state
encoding are selected.

`max_k` remains the PDR frame-iteration budget. An enabled age check uses at
least its candidate age as the run budget so a counterexample at that monitor
age can reach exact `F[0]`. This adjustment is confined to the enabled age flow.

Set `KEPLER_SEC_DIAG=1` to print the certified or fallback age selected for each
output range.

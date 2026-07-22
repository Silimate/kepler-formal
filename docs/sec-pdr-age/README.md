# Dual-Rail PDR Age Discovery

This document describes automatic age discovery for SEC runs using the PDR
engine and `dual_rail_steady` encoding. The flow finds a cycle age after which
the selected public outputs of both designs are proved binary-defined. SEC can
then prove concrete output equality without treating a persistent unknown value
as a concrete proof.

The feature is disabled by default. Enable it explicitly with
`--sec-pdr-auto-age` or `sec_pdr_auto_age: true`. Without that opt-in, SEC
requires both outputs to be binary-defined starting at cycle zero.

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
- The defined-value difference property always starts at the exact initial
  state and is never moved by age discovery.

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

## Defined-Value Difference Property

PDR first checks this safety property once for each output batch:

```text
NOT (both designs are binary-defined AND their values are opposite)
```

This property starts at cycle zero and covers every reachable cycle. An X value
does not violate it. `Different` therefore identifies a real `01` versus `10`
counterexample. `Equivalent` proves that no such counterexample is reachable.
`Inconclusive` leaves the affected output unresolved and cannot be repaired by
moving the definedness age.

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
6. If the maximum is not proved for a single output, report that output as
   inconclusive.

Each age property is monotone: once all selected outputs are proved defined from
age `N`, the same certificate holds for any larger candidate age.

## Final Verdict

An output is proved only when both independent safety obligations converge:

1. No defined-value difference is reachable from cycle zero.
2. Both outputs are binary-defined from a certified age `N` onward.

A defined-value counterexample reports `Different`. If definedness is not
certified, the output remains `Inconclusive`; equal `X/X` rails are not accepted
as a proof. The result names affected public outputs and explains when unknown
data propagated from uninitialized sequential logic.

## Disabled Flow

With automatic age discovery disabled, the monitor and all age probes are
absent. SEC checks the defined-value difference property from the original
`F[0]`, then requires both outputs to be binary-defined from cycle zero. A
persistent or initial X therefore yields `Inconclusive`, not `Proved`.

## Reused Work

Output batches and age probes share only property-independent model work within
the same transition system:

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
| `--sec-pdr-auto-age` | `sec_pdr_auto_age: true` | disabled | Enable automatic age discovery. |
| `--no-sec-pdr-auto-age` | `sec_pdr_auto_age: false` | disabled | Disable age search and require definedness from cycle zero. |
| `--sec-pdr-age-min N` | `sec_pdr_age_min: N` | `10` | First candidate age. |
| `--sec-pdr-age-max N` | `sec_pdr_age_max: N` | `20` | Last candidate age. |

Both ages are non-negative integers and the minimum must not exceed the
maximum. Explicit age options are rejected unless PDR and dual-rail steady-state
encoding are selected.

`max_k` is the PDR frame-iteration budget for both normal and age-monitor
properties. If either configured age exceeds `max_k`, SEC caps it to `max_k`
and emits a warning. Age discovery never silently deepens the requested run.

Set `KEPLER_SEC_DIAG=1` to print the defined-value and definedness result for
each output range, including any certified age.

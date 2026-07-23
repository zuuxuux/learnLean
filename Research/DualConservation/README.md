# Dual Conservation Lean Formalization

This project formalizes the accounting kernel of risk-budgeted recursive
agent delegation. A root agent carries two affine capabilities:

- deterministic reserve; and
- statistical miscoverage budget (`alpha`).

Both split rather than copy. Alpha uses four phases:

- `free`;
- `pending` and provably unexposed;
- `exposed` and burned; and
- `observed` and burned.

The distinction between exposure and observation is deliberate. If an action
creates the certified risk event and its result is then lost, the exposure still
occurred. A correct runtime therefore burns alpha no later than the earliest
risk-creating step and records outcome observation separately.

The main declarations are:

- `dual_conservation_probability`: local reserve and alpha allocations imply a
  fleet-level aggregate-loss bound without independence;
- `DelegationTree.recursive_dual_conservation`: local split checks imply root
  conservation over every finite binary delegation tree;
- `fleet_confidence_no_cloning`: copying a positive allowance to two or more
  children exceeds the parent allowance;
- `two_attempt_refund_unsound`: success-based reuse breaks a nontrivial
  end-to-end allowance after two independent attempts;
- `AlphaReachable.burned_mono` and `exposure_irreversible`: exposure-burned
  alpha cannot return to free or pending state; and
- `AlphaReachable.observed_mono` and `observation_irreversible`: outcomes visible
  to control logic cannot become unobserved.

## Run

```text
lake update
lake exe cache get
lake build
lake env leanchecker
```

Pinned environment:

- Lean `v4.32.0-rc1`;
- Mathlib `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.

The exact source passed GitHub Actions run `30008862231`: a clean 8,581-job
build and the bundled `leanchecker` environment check. It contains no `sorry`,
`admit`, `unsafe` declaration, or user-declared axiom.

An independently implemented `nanoda` check was attempted after a successful
Lean environment export. It did not complete because its parser rejected the
exported environment, so no independent-kernel claim is made.

## Research status

The Lean proofs establish the statements under the definitions in this
repository. They do not establish literature priority. The associated research
note treats the systems contribution as a falsifiable candidate synthesis:
statistical miscoverage becomes recursively delegated affine execution state,
bound before exposure, burned at exposure, separately marked at observation,
and replaceable only through a proof that preserves a named global risk
invariant.

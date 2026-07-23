# Dual Conservation for Recursive Agents

This project formalizes a proposed systems law for agentic delegation:

> A recursive agent must split both its deterministic authority and its
> statistical confidence budget. Neither may be copied, and confidence used to
> observe an outcome may not be refunded.

The first capability is ordinary reserve: money, irreversible actions, API
quota, write scope, or another material loss budget. The second is an `alpha`
budget: the maximum acceptable probability that a locally certified action or
an entire delegated run violates its stated bound.

## Checked results

`DualConservation.lean` contains proofs of:

- `adaptive_global_failure_bound`: arbitrarily dependent first-failure events
  compose under additive alpha allocation. No independence assumption is used.
- `dual_conservation_probability`: local reserve bounds plus local alpha bounds
  imply a fleet-level bound on aggregate reserve exceedance.
- `DelegationTree.recursive_dual_conservation`: local split constraints at every
  fork imply global conservation over every terminal agent in an arbitrarily
  deep binary delegation tree.
- `fleet_confidence_no_cloning`: copying any positive confidence allowance to
  two or more children exceeds the parent allowance.
- `two_use_confidence_recycling_unsound`: even two independent reuses of a
  positive allowance `p` produce failure probability `1 - (1-p)^2 > p`.
- `AlphaReachable.burned_mono`: once alpha has funded an observed outcome, it
  cannot return to the free pool under the trusted protocol.

There are no `sorry` declarations.

## Build

The project pins both Mathlib and its matching Lean release candidate.

```sh
lake update
lake exe cache get
lake build
```

The included GitHub workflow also requests the independent `nanoda` checker and
forbids `sorryAx`.

## Status of the research claim

The Lean proofs establish the mathematical statements under the definitions in
this repository. They do not by themselves establish literature priority. The
associated research note separates the proved claims from the candidate-novel
systems synthesis and documents the closest prior art.

import Lake
open Lake DSL

package DualConservation where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56"

@[default_target]
lean_lib DualConservation

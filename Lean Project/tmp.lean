import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a b : Int) : natAbs (a - b) ≤ natAbs a + natAbs b := by
trace_state

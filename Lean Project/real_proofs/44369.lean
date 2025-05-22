import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example (n : Nat) : natAbs (negOfNat n) = n := by
  cases n <;> rfl
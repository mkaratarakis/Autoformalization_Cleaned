import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (n : Nat) : natAbs (negOfNat n) = n := by
  cases n
  · simp [negOfNat, natAbs]
  · simp [negOfNat, natAbs]

/- ACTUAL PROOF OF Int.natAbs_negOfNat -/

example (n : Nat) : natAbs (negOfNat n) = n := by
  cases n <;> rfl
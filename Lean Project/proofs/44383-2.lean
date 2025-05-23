import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example : 0 < natAbs a ↔ a ≠ 0 := by
  constructor
  · intro h
    by_cases h1 : a = 0
    exact h1
    contradiction
  · intro h
    apply Nat.pos_of_ne_zero
    rw [natAbs_eq_zero]
    push_neg at h
    exact h

/- ACTUAL PROOF OF Int.natAbs_pos -/

example : 0 < natAbs a ↔ a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, natAbs_eq_zero]
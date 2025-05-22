import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  by_contradiction hb
  apply hb
  apply mul_nonneg
  · apply zero_le
  · exact le_of_eq (Nat.eq_zero_of_le_zero hb)

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_left -/

example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  apply Decidable.by_contra
  intros
  simp_all
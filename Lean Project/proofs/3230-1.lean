import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x z : Nat) {y : Nat} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero =>
    simp
    simp [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le H (Nat.zero_le _))]
  | succ z ih =>
    simp
    rw [Nat.mul_succ]
    rw [add_assoc]
    rw [Nat.div_add_one_of_lt (Nat.lt_of_lt_of_le H (Nat.zero_le _))]
    rw [ih]
    rfl

/- ACTUAL PROOF OF Nat.add_mul_div_left -/

example (x z : Nat) {y : Nat} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl
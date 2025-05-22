import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n with
  | zero =>
    simp [MulZeroClass.mul_zero, div_zero]
  | succ k ih =>
    rw [mul_succ, add_mul_div_cancel _ _ (Nat.succ_pos _)]
    rw [ih]

/- ACTUAL PROOF OF Nat.mul_div_right -/

example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]
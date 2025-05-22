import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n with
  | zero =>
    rw [MulZeroClass.mul_zero, Nat.div_zero]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_div_cancel_left H]
    rw [ih]

/- ACTUAL PROOF OF Nat.mul_div_right -/

example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]
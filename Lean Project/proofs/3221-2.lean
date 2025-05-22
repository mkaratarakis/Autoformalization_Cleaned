import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n with
  | zero =>
    simp [zero_mul]
    simp [Nat.div_zero]
  | succ k ih =>
    simp [Nat.mul_succ, Nat.div_add_cancel_left H]
    simp [ih]

/- ACTUAL PROOF OF Nat.mul_div_right -/

example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]
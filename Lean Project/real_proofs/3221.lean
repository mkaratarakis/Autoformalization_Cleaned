import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (n : Nat) {m : Nat} (H : 0 < m) : m * n / m = n := by
  induction n <;> simp_all [mul_succ]
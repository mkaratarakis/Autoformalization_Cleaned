import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction' a with d hd
  · -- Base case: a = 0
    exfalso
    exact a0
  · -- Inductive step: a = d + 1
    rw [Nat.mulSucc, Nat.mulSucc]
    rw [hd]
    exact Iff.rfl

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
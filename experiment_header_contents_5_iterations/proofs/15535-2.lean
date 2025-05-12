import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction' a with n ih
  · -- Base case: a = 0
    simp
  · -- Inductive step: a = n + 1
    simp [Nat.succ_mul]
    rw [add_lt_add_iff_left]
    apply ih
    exact Nat.zero_lt_succ n

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
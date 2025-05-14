import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.strong_rec with
  | zero => exact iff_of_false (not_lt_zero _) (not_lt_zero _)
  | succ n ih =>
    unfold Nat.succ
    rw [Nat.mul_succ, Nat.mul_succ]
    simp
    rw [Nat.add_assoc, Nat.add_assoc, ih]
    rw [Nat.add_succ, Nat.add_succ]
    rw [Nat.add_lt_add_iff_left]
    rw [Nat.add_lt_add_iff_left]
    rw [← Nat.add_succ]
    rw [← Nat.add_succ, Nat.succ_lt_succ_iff]
    rw [Nat.succ_lt_succ_iff]

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
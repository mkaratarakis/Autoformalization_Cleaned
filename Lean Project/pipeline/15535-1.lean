import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction' a using Nat.strong_induction_on with n ih
  case zero =>
    simp
  case succ =>
    simp at a0
    cases a0
    simp [Nat.mul_succ, Nat.add_lt_add_iff_left]
    apply ih
    exact Nat.zero_lt_succ _

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.recOn with
  | zero =>
    exact iff_of_false (not_lt_of_ge (zero_le _)) (not_lt_of_ge (zero_le _))
  | succ n ih =>
    simp [Nat.succ_mul]
    constructor
    · intro h
      apply lt_of_add_lt_add_left
      . exact zero_lt_succ n
      . assumption
    · intro h
      apply add_lt_add_right
      . assumption
      . exact zero_lt_succ n

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
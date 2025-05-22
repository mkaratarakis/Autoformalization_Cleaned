import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.strongRecOn with
  | ind d hd =>
    have : d * b < d * c ↔ b < c := hd d (Nat.lt_succ_self d) (Nat.pos_of_ne_zero (Nat.succ_ne_zero d))
    rw [this]
    constructor
    · intro h
      apply Nat.lt_of_add_lt_add_left
      · apply Nat.lt_succ_self
      · rw [Nat.succ_mul]
        rw [Nat.mul_succ]
        exact h
    · intro h
      rw [Nat.mul_succ]
      rw [Nat.succ_mul]
      apply Nat.lt_of_add_lt_add_left
      · apply Nat.lt_succ_self
      · exact h

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
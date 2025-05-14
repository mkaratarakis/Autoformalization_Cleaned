import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.rec with
  | zero =>
    simp
  | succ n ih =>
    simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add]
    constructor
    . intros h
      cases Nat.eq_zero_or_pos n with
      | inl hn =>
        rw [hn] at h
        exact Nat.not_lt_zero _ h
      | inr hn =>
        exact lt_of_add_lt_add_left (Nat.mul_lt_mul_of_pos_left h hn) _
    . intros h
      apply Nat.add_lt_add_left
      exact Nat.mul_lt_mul_of_pos_left h n.succ_pos

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
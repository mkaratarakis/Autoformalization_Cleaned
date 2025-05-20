import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.rec with
  | zero =>
    -- Base case: a = 0
    -- The assumption 0 < 0 is false, so the implication is trivially true.
    simp
  | succ n ih =>
    -- Inductive step: a = n + 1
    -- We need to show (n + 1) * b < (n + 1) * c ↔ b < c
    simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add]
    -- Now the goal is n * b + b < n * c + c ↔ b < c
    apply ih
    -- The inductive hypothesis gives us n * b < n * c ↔ b < c
    -- Adding b to both sides preserves the inequality
    simp [Nat.add_lt_add_iff_left]
    -- The goal is now trivially true by the inductive hypothesis
    exact ih

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega
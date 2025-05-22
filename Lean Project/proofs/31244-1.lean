import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (h : i < a) : 0 < a - i := by
  induction a with
  | zero =>
    -- Base case: a = 0
    -- This case is vacuously true because i < 0 is impossible for natural numbers.
    exfalso
    apply Nat.not_lt_zero
    exact h
  | succ a ih =>
    -- Inductive step: a = succ a
    cases h with
    | zero =>
      -- Case 1: i = 0
      -- We need to show 0 < succ a - 0
      apply Nat.zero_lt_succ
      assumption
    | succ i h =>
      -- Case 2: i = succ i
      -- We need to show 0 < succ a - succ i
      -- By the induction hypothesis, 0 < a - i
      have ih_app : 0 < a - i := ih h
      -- We know that a - i ≤ succ a - succ i
      have le_step : a - i ≤ succ a - succ i := by
        simp
        apply Nat.le_succ
      -- By the transitivity of less-than and less-than-or-equal, 0 < succ a - succ i
      exact Nat.lt_of_lt_of_le ih_app le_step

/- ACTUAL PROOF OF Nat.zero_lt_sub_of_lt -/

example (h : i < a) : 0 < a - i := by
  induction a with
  | zero => contradiction
  | succ a ih =>
    match Nat.eq_or_lt_of_le h with
    | Or.inl h => injection h with h; subst h; rw [Nat.add_sub_self_left]; decide
    | Or.inr h =>
      have : 0 < a - i := ih (Nat.lt_of_succ_lt_succ h)
      exact Nat.lt_of_lt_of_le this (Nat.sub_le_succ_sub _ _)
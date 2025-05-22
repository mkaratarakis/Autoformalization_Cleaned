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
    | refl =>
      -- Case 1: i = a + 1
      -- This case is impossible because i < a + 1 and i = a + 1 cannot both be true.
      apply Nat.not_lt_zero
      assumption
    | step i' h' =>
      -- Case 2: i = succ i'
      -- We need to show 0 < succ a - succ i'
      -- By the induction hypothesis, 0 < a - i'
      exact Nat.succ_lt_succ (ih h')

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
import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (h : i < a) : 0 < a - i := by
  induction a with
  | zero => contradiction
  | succ a ih =>
    match Nat.eq_or_lt_of_le h with
    | Or.inl h => injection h with h; subst h; rw [Nat.add_sub_self_left]; decide
    | Or.inr h =>
      have : 0 < a - i := ih (Nat.lt_of_succ_lt_succ h)
      exact Nat.lt_of_lt_of_le this (Nat.sub_le_succ_sub _ _)
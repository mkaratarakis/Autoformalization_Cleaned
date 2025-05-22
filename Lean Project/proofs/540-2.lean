import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example {l : List α} {k : Nat} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  induction l generalizing l' with
  | nil =>
    -- Base case: l = []
    -- The assumption k < length [] is false, so the goal is trivially true.
    trivial
  | cons x l ih =>
    -- Inductive step: l = x :: l
    cases k with
    | zero =>
      -- Subcase: k = 0
      rfl
    | succ k =>
      -- Subcase: k = k' + 1
      simp
      rw [length] at hk
      rw [Nat.succ_lt_succ_iff] at hk
      exact ih hk l'

/- ACTUAL PROOF OF List.eraseIdx_append_of_lt_length -/

example {l : List α} {k : Nat} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  induction l generalizing k with
  | nil => simp_all
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k => simp_all [eraseIdx_cons_succ, Nat.succ_lt_succ_iff]
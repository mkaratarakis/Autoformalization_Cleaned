import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example {l : List α} {k : Nat} (hk : length l ≤ k) (l' : List α) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - length l) := by
  induction l generalizing k with
  | nil =>
    simp only [length, eraseIdx, zero_sub]
  | cons x l ih =>
    cases k with
    | zero =>
      simp only [eraseIdx, length, Nat.succ_sub_one, Nat.sub_self]
    | succ k =>
      simp only [length, eraseIdx, Nat.succ_sub_succ, Nat.sub_succ]
      rw [ih (Nat.le_step (Nat.le_of_succ_le_succ hk))]
      rfl

/- ACTUAL PROOF OF List.eraseIdx_append_of_length_le -/

example {l : List α} {k : Nat} (hk : length l ≤ k) (l' : List α) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - length l) := by
  induction l generalizing k with
  | nil => simp_all
  | cons x l ih =>
    cases k with
    | zero => simp_all
    | succ k => simp_all [eraseIdx_cons_succ, Nat.succ_sub_succ]
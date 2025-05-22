import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} {a : α} :
    (l.set m a).drop n = if m < n then l.drop n else (l.drop n).set (m - n) a := by
  induction n with
  | zero =>
    rw [drop, if_neg (Nat.not_lt_zero _)]
    rfl
  | succ n ih =>
    match l with
    | [] =>
      rw [drop, set_nil, if_neg (Nat.not_lt_zero _)]
      rfl
    | h :: t =>
      match m with
      | 0 =>
        rw [set_cons_head, drop, if_pos rfl]
        rfl
      | m' + 1 =>
        rw [set_cons_tail, drop_cons]
        split
        · intro h1
          rw [ih h1]
          rfl
        · intro h1
          rw [ih h1, drop, set, Nat.succ_sub_succ]
          rfl

/- ACTUAL PROOF OF List.drop_set -/

example {l : List α} {n m : Nat} {a : α} :
    (l.set m a).drop n = if m < n then l.drop n else (l.drop n).set (m - n) a := by
  induction n generalizing l m with
  | zero => simp
  | succ _ hn =>
    cases l with
    | nil => simp
    | cons hd tl =>
      cases m
      · simp_all
      · simp only [hn, set_cons_succ, drop_succ_cons, succ_lt_succ_iff]
        congr 2
        exact (Nat.add_sub_add_right ..).symm
import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} {a : α} :
    (l.set m a).drop n = if m < n then l.drop n else (l.drop n).set (m - n) a := by
  induction n with
  | zero =>
    simp [set, drop]
  | succ n ih =>
    cases l with
    | nil =>
      simp [set, drop]
    | cons hd tl =>
      cases m with
      | zero =>
        simp [set, drop]
      | succ m =>
        simp [set, drop, ih]
        rw [Nat.sub_succ_sub]
        simp

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
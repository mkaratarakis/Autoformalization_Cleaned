import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n)[m]? = none := by
  rw [take.eq_def]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    cases h with
    | refl =>
      simp
    | step h =>
      have h' : n ≤ m := by
        exact Nat.le_of_succ_le_succ h
      simp [ih h']

/- ACTUAL PROOF OF List.get?_take_eq_none -/

example {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n).get? m = none := by
  simp [getElem?_take_eq_none h]
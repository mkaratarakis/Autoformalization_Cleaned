import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n).get? m = none := by
  rw [take]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    cases h with
    | zero =>
      simp
    | succ m ih =>
      simp [ih]

/- ACTUAL PROOF OF List.get?_take_eq_none -/

example {l : List α} {n m : Nat} (h : n ≤ m) :
    (l.take n).get? m = none := by
  simp [getElem?_take_eq_none h]
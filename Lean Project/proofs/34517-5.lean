import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} {a : α} :
    (l.set m a).take n = (l.take n).set m a := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    cases l with
    | nil =>
      simp
    | cons hd tl =>
      by_cases h : m = 0
      · simp [h]
      · simp
        rw [setCons, ih (hd :: tl) (Nat.pred m) a]
        simp [set]

/- ACTUAL PROOF OF List.set_take -/

example {l : List α} {n m : Nat} {a : α} :
    (l.set m a).take n = (l.take n).set m a := by
  induction n generalizing l m with
  | zero => simp
  | succ _ hn =>
    cases l with
    | nil => simp
    | cons hd tl => cases m <;> simp_all
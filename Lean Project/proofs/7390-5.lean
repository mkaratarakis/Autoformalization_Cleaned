import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (l : List α) (n : Nat) :
    (l.drop n).head? = l[n]? := by
  cases n with
  | zero =>
    show l.head? = l[0]?
    cases l with
    | nil => rfl
    | x :: xs => rfl
  | succ n =>
    rw [drop_succ, head?_cons]
    rfl

/- ACTUAL PROOF OF List.head?_drop -/

example (l : List α) (n : Nat) :
    (l.drop n).head? = l[n]? := by
  rw [head?_eq_getElem?, getElem?_drop, Nat.add_zero]
import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example : findSome? f (replicate n a) = if n = 0 then none else f a := by
  cases n with
  | zero =>
    simp [findSome?, replicate]
  | succ n =>
    simp [findSome?, replicate]
    rw [ite_succ]
    apply findSome?_eq_of_cons_ne_none
    simp [findSome?, replicate]
    rfl

/- ACTUAL PROOF OF List.findSome?_replicate -/

example : findSome? f (replicate n a) = if n = 0 then none else f a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, findSome?_cons]
    split <;> simp_all
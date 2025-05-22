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
    cases h : f a
    · simp [h]
    · rw [findSome?_cons_none]
      simp

/- ACTUAL PROOF OF List.findSome?_replicate -/

example : findSome? f (replicate n a) = if n = 0 then none else f a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, findSome?_cons]
    split <;> simp_all
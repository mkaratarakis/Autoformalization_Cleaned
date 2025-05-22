import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil =>
    -- Base case: xs = []
    exfalso
    apply Option.noConfusion w
    · rintro ⟨⟩
  | cons x xs ih =>
    -- Inductive step: xs = x :: xs'
    by_cases h : p x
    · -- Case 1: p x = true
      rw [findIdx_eq_zero_iff_head.mpr h] at w
      injection w with w
      exact h
    · -- Case 2: p x = false
      rw [findIdx_cons_of_not_head _ _ h]
      rw [get?_cons_of_nat_ne_zero]
      · apply ih
        · rw [findIdx_cons_of_not_head _ _ h] at w
          exact w
      · exact zero_ne_succ _

/- ACTUAL PROOF OF List.findIdx_of_get?_eq_some -/

example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]
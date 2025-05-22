import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example {xs : List α} (w : xs[xs.findIdx? p]? = some y) : p y := by
  induction xs with
  | nil =>
    exfalso
    apply Option.noConfusion w
    · rintro ⟨⟩
  | cons x xs ih =>
    by_cases h : p x
    · rw [findIdx?_eq_zero_iff_head.mpr h] at w
      injection w with w
      exact h
    · rw [findIdx?_cons_of_not_head _ _ h]
      rw [get?_cons_of_nat_ne_zero]
      · apply ih
        · rw [findIdx?_cons_of_not_head _ _ h] at w
          exact w
      · exact zero_ne_succ _

/- ACTUAL PROOF OF List.findIdx_of_get?_eq_some -/

example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]
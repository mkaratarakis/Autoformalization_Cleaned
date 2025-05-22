import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example {α : Type} {p : α → Bool} {xs : List α} {y : α} (w : xs[xs.findIdx? p]? = some y) : p y := by
  induction xs with
  | nil =>
    exfalso
    apply Option.noConfusion w
    · rintro ⟨⟩
  | cons x xs ih =>
    by_cases h : p x
    · rw [findIdx?_head] at w
      injection w with w
      exact h
    · rw [findIdx?_tail _ _ h] at w
      rw [get?_cons_of_nat_ne_zero] at w
      · apply ih
        · rw [findIdx?_tail _ _ h] at w
          exact w
      · exact zero_ne_succ _

/- ACTUAL PROOF OF List.findIdx_of_get?_eq_some -/

example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]
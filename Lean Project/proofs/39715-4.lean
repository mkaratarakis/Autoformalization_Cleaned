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
    · rw [Option.some.injEq, findIdx?_eq_zero] at w
      · exact h
      · rfl
    · rw [findIdx?_ne_zero h] at w
      rw [get?_cons_ne_zero] at w
      · apply ih
        · rw [findIdx?_ne_zero h] at w
          exact w
      · exact Nat.succ_ne_zero _

/- ACTUAL PROOF OF List.findIdx_of_get?_eq_some -/

example {xs : List α} (w : xs.get? (xs.findIdx p) = some y) : p y := by
  induction xs with
  | nil => simp_all
  | cons x xs ih => by_cases h : p x <;> simp_all [findIdx_cons]
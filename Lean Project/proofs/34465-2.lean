import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases p a = true
    case pos =>
      by_cases q a = true
      case pos =>
        simp only [filter, takeWhile, cons_self, ih]
        rfl
      case neg =>
        simp only [filter, takeWhile, cons_self, ih]
        rfl
    case neg =>
      simp only [filter, takeWhile, cons_self, ih]
      rfl

/- ACTUAL PROOF OF List.takeWhile_filter -/

example (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, takeWhile_filterMap]
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
        simp only [filter, takeWhile, ih]
        exact takeWhile_cons_of_pos _ _ ih
      case neg =>
        simp only [filter, takeWhile, ih]
        exact takeWhile_cons_of_neg _ _ ih
    case neg =>
      simp only [filter, takeWhile, ih]
      exact takeWhile_cons_of_neg _ _ ih

/- ACTUAL PROOF OF List.takeWhile_filter -/

example (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, takeWhile_filterMap]
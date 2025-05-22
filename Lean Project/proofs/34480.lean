import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p q : α → Bool) (l : List α) :
    (l.filter p).dropWhile q = (l.dropWhile fun a => !p a || q a).filter p := by
  rw [← filterMap_eq_filter, dropWhile_filterMap]
  simp
  rfl

/- ACTUAL PROOF OF List.dropWhile_filter -/

example (p q : α → Bool) (l : List α) :
    (l.filter p).dropWhile q = (l.dropWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, dropWhile_filterMap]
import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example (f : α → Bool) (l : List α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  apply eraseP_eq_of_filter_eq
  · intro x
    simp only [and_true, Option.guard, filterMap, eraseP]
    split
    · intro h
      simp [h]
    · intro h
      simp [h]
  · intro x
    simp only [and_false, Option.guard, filterMap, eraseP]
    split
    · intro h
      simp [h]
    · intro h
      simp [h]

/- ACTUAL PROOF OF List.eraseP_filter -/

example (f : α → Bool) (l : List α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  rw [← filterMap_eq_filter, eraseP_filterMap]
  congr
  ext x
  simp only [Option.guard]
  split <;> split at * <;> simp_all
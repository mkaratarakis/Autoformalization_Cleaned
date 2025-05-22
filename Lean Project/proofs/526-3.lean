import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example (f : α → Bool) (l : List α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h₁ : f hd = true
    · by_cases h₂ : p hd = true
      · simp [h₁, h₂, eraseP, filter]
        rw [ih]
      · simp [h₁, h₂, eraseP, filter]
        rw [ih]
    · simp [h₁, eraseP, filter]
      rw [ih]

/- ACTUAL PROOF OF List.eraseP_filter -/

example (f : α → Bool) (l : List α) :
    (filter f l).eraseP p = filter f (l.eraseP (fun x => p x && f x)) := by
  rw [← filterMap_eq_filter, eraseP_filterMap]
  congr
  ext x
  simp only [Option.guard]
  split <;> split at * <;> simp_all
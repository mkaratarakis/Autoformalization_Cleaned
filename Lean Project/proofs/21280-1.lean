import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @List.filterMap = @filterMapTR := by
  funext α β f l
  induction l with
  | nil =>
    simp [filterMap, filterMapTR]
  | cons hd tl ih =>
    simp [filterMap, filterMapTR]
    cases h : f hd with
    | none =>
      simp [filterMap, filterMapTR, h]
      rw [ih]
    | some v =>
      simp [filterMap, filterMapTR, h]
      rw [ih]
      rfl

/- ACTUAL PROOF OF List.filterMap_eq_filterMapTR -/

example : @List.filterMap = @filterMapTR := by
  funext α β f l
  let rec go : ∀ as acc, filterMapTR.go f as acc = acc.data ++ as.filterMap f
    | [], acc => by simp [filterMapTR.go, filterMap]
    | a::as, acc => by
      simp only [filterMapTR.go, go as, Array.push_data, append_assoc, singleton_append, filterMap]
      split <;> simp [*]
  exact (go l #[]).symm
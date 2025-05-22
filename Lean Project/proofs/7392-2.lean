import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  rw [zipWith, length_map, length_min, min_def] at h
  simp at h
  cases' h with h h
  · exact h
  · exact h

/- ACTUAL PROOF OF List.lt_length_right_of_zipWith -/

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  rw [length_zipWith] at h; omega
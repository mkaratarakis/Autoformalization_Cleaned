import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  have h1 : (zipWith f l l').length = min l.length l'.length := by
    simp [zipWith, List.length]
  rw [h1] at h
  exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)

/- ACTUAL PROOF OF List.lt_length_left_of_zipWith -/

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  rw [length_zipWith] at h; omega
import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  simp only [zipWith, length] at h
  simp only [min_def, length] at h
  cases h with
  | inl h =>
    exact h
  | inr h =>
    exact Nat.le_trans (Nat.le_of_lt h) (min_le_right (length l) (length l'))

/- ACTUAL PROOF OF List.lt_length_right_of_zipWith -/

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length := by
  rw [length_zipWith] at h; omega
import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  rw [zipWith_length] at h
  exact min_le_of_left_le (h.trans (min_le_right _ _))

/- ACTUAL PROOF OF List.lt_length_left_of_zipWith -/

example {f : α → β → γ} {i : Nat} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length := by
  rw [length_zipWith] at h; omega
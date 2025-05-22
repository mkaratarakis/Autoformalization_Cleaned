import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (L : List α) {i j : Nat} (h : i + j < L.length) : j < (L.drop i).length := by
  have h₁ : i ≤ i + j := le_add_right i j
  have h₂ : i + j < L.length := h
  have h₃ : i < L.length := Nat.lt_trans (Nat.lt_add_right i j) h
  have h₄ : L = L.take i ++ L.drop i := List.take_drop_append L i
  rw [h₄] at h₂
  simp only [length_take, length_append, min_eq_left h₃] at h₂
  exact Nat.sub_lt h₂ (Nat.add_le_add_right h₁ j)

/- ACTUAL PROOF OF List.lt_length_drop -/

example (L : List α) {i j : Nat} (h : i + j < L.length) : j < (L.drop i).length := by
  have A : i < L.length := Nat.lt_of_le_of_lt (Nat.le.intro rfl) h
  rw [(take_append_drop i L).symm] at h
  simpa only [Nat.le_of_lt A, Nat.min_eq_left, Nat.add_lt_add_iff_left, length_take,
    length_append] using h
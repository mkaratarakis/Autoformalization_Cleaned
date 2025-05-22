import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  induction l₁ with
  | nil =>
    simp [take, append]
    exact (Nat.eq_zero_of_le_zero (Nat.le_of_eq h)).symm
  | cons hd tl ih =>
    simp [take, append]
    rw [ih (Nat.pred_eq h)]
    rfl

/- ACTUAL PROOF OF List.take_left' -/

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
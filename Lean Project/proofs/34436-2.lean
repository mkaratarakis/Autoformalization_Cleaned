import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [take_append_left h]
  rfl

/- ACTUAL PROOF OF List.take_left' -/

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
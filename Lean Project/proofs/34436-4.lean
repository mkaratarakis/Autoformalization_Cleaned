import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  induction l₁ with
  | nil =>
    simp [take, append]
  | cons hd tl ih =>
    simp [take, append, ih]

/- ACTUAL PROOF OF List.take_left' -/

example {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply take_left
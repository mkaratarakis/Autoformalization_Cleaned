import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (f : α → β → γ) (l₁ l₂) :
    length (zipWith f l₁ l₂) = min (length l₁) (length l₂) := by
  induction l₁ generalizing l₂ <;> cases l₂ <;>
    simp_all [succ_min_succ, Nat.zero_min, Nat.min_zero]
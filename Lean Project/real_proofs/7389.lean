import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat


example (l₁ : List α) (l₂ : List β) :
    length (zip l₁ l₂) = min (length l₁) (length l₂) := by
  simp [zip]
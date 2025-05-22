import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example (l₁ l₂) : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  rw [countP]
  rw [Filter.filter]
  rw [List.append]
  rw [List.length_append]
  rw [countP]
  rw [countP]
  rfl

/- ACTUAL PROOF OF List.countP_append -/

example (l₁ l₂) : countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂ := by
  simp only [countP_eq_length_filter, filter_append, length_append]
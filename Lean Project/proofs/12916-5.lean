import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Sublist
open Nat
variable (p q : α → Bool)

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  unfold countP
  rw [countP.go.eq_def]
  simp
  exact Nat.le_trans (length_le_length_of_sublist s) (length_filter_le_length _ _)

/- ACTUAL PROOF OF List.Sublist.countP_le -/

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  simp only [countP_eq_length_filter]
  apply s.filter _ |>.length_le
import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Sublist
open Nat
variable (p q : α → Bool)

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  unfold countP
  apply Nat.le_intro
  rw [length_filter_le_length_filter_of_sublist]
  exact s

/- ACTUAL PROOF OF List.Sublist.countP_le -/

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  simp only [countP_eq_length_filter]
  apply s.filter _ |>.length_le
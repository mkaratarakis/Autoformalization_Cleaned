import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Sublist
open Nat
variable (p q : α → Bool)

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  unfold countP
  apply length_le_of_sublist
  apply filter_sublist_of_sublist
  exact s

/- ACTUAL PROOF OF List.Sublist.countP_le -/

example (s : l₁ <+ l₂) : countP p l₁ ≤ countP p l₂ := by
  simp only [countP_eq_length_filter]
  apply s.filter _ |>.length_le
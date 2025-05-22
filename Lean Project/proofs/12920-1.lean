import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example {l : List α} : (l.countP fun _ => false) = 0 := by
  apply List.countP_eq_zero
  intros a h
  simp only [not_false_eq_true]
  rfl

/- ACTUAL PROOF OF List.countP_false -/

example {l : List α} : (l.countP fun _ => false) = 0 := by
  rw [countP_eq_zero]
  simp
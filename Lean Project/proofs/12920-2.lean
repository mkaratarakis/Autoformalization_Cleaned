import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example {l : List α} : (l.countP fun _ => false) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp [countP]
    rw [ih]
    simp only [not_false_eq_true, Bool.not_eq_true, Bool.false_ne_true]

/- ACTUAL PROOF OF List.countP_false -/

example {l : List α} : (l.countP fun _ => false) = 0 := by
  rw [countP_eq_zero]
  simp
import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example {l : List α} : (l.countP fun _ => true) = l.length := by
  induction l with
  | nil =>
    rfl
  | cons hd tl ih =>
    simp [countP]
    rw [ih]
    simp [length]

/- ACTUAL PROOF OF List.countP_true -/

example {l : List α} : (l.countP fun _ => true) = l.length := by
  rw [countP_eq_length]
  simp
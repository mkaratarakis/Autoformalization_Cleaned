import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example {l : List α} : (l.countP fun _ => true) = l.length := by
  induction l with
  | nil =>
    simp [countP, length]
  | cons hd tl ih =>
    simp [countP, length]
    rw [ih]

/- ACTUAL PROOF OF List.countP_true -/

example {l : List α} : (l.countP fun _ => true) = l.length := by
  rw [countP_eq_length]
  simp
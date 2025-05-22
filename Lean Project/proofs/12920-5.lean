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
    have : countP (fun _ => false) tl = 0 := ih
    rw [this]
    rfl

/- ACTUAL PROOF OF List.countP_false -/

example {l : List α} : (l.countP fun _ => false) = 0 := by
  rw [countP_eq_zero]
  simp
import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example (l) : countP.go p l n = n + countP.go p l 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    unfold countP.go
    rw [ih (n := n + 1), ih (n := n), ih (n := 1)]
    if h : p head then simp [h, Nat.add_assoc] else simp [h]
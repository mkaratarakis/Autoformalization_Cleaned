import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example (l) (pa : ¬p a) : countP p (a :: l) = countP p l := by
  unfold countP
  simp [countP.go]
  cases h : p a
  · exact pa h
  · rfl

/- ACTUAL PROOF OF List.countP_cons_of_neg -/

example (l) (pa : ¬p a) : countP p (a :: l) = countP p l := by
  simp [countP, countP.go, pa]
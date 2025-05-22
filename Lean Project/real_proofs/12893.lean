import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example (l) (pa : ¬p a) : countP p (a :: l) = countP p l := by
  simp [countP, countP.go, pa]
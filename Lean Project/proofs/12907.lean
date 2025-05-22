import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (a : α) (l : List α) : count a (a :: l) = count a l + 1 := by
  rw [count]
  simp [count]

/- ACTUAL PROOF OF List.count_cons_self -/

example (a : α) (l : List α) : count a (a :: l) = count a l + 1 := by
  simp [count_cons]
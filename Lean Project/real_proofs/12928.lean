import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]


example (ab : a ≠ b) (l : List α) : count a (l.erase b) = count a l := by
  rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]
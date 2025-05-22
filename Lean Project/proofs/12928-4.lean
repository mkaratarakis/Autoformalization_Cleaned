import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (ab : a ≠ b) (l : List α) : count a (l.erase b) = count a l := by
  rw [count_erase]
  rw [dif_neg ab]
  rfl

/- ACTUAL PROOF OF List.count_erase_of_ne -/

example (ab : a ≠ b) (l : List α) : count a (l.erase b) = count a l := by
  rw [count_erase, if_neg (by simpa using ab.symm), Nat.sub_zero]
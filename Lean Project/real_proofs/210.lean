import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]


example [LawfulBEq α] (a : α) (l : List α) : (a :: l).erase a = l := by
  simp [erase_cons]
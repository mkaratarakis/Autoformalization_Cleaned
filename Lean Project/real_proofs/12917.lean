import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]


example (a b : α) (l : List α) :
    count a (b :: l) = count a l + if b == a then 1 else 0 := by
  simp [count, countP_cons]
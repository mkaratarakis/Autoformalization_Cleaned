import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]


example (a b : α) : count a [b] = if b == a then 1 else 0 := by
  simp [count_cons]
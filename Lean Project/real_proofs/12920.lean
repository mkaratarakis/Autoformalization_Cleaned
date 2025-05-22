import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example {l : List α} : (l.countP fun _ => false) = 0 := by
  rw [countP_eq_zero]
  simp
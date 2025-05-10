import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}


example (l : List α) (n) : get? (enum l) n = (get? l n).map fun a => (n, a) := by
  simp
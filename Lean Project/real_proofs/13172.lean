import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}


example (n) (l : List α) (m) :
    get? (enumFrom n l) m = (get? l m).map fun a => (n + m, a) := by
  simp
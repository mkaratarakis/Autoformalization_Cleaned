import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}


example (l : List α) (n) (i : Fin (l.enumFrom n).length) :
    (l.enumFrom n).get i = (n + i, l.get (i.cast enumFrom_length)) := by
  simp
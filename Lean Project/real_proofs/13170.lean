import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}


example (l : List α) (i : Fin l.enum.length) :
    l.enum.get i = (i.1, l.get (i.cast enum_length)) := by
  simp
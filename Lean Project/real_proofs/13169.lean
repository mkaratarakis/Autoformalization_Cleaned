import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Enum

open List
variable {α β : Type*}


example {x : ℕ × α} {l : List α} : x ∈ enum l ↔ l.get? x.1 = x.2 := by
  simp [mem_enum_iff_getElem?]
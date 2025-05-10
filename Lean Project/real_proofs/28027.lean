import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Option.Defs

open Option
variable {α : Type*} {β : Type*}


example {α : Type*} {a b : α} : a ∈ some b ↔ b = a := by
  simp
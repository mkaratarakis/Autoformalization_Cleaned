import Mathlib.Logic.Function.Defs
import Batteries.Tactic.Init
import Mathlib.Data.Option.NAry

open Option
open Function
variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}


example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂, bind_eq_some]
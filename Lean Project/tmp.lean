import Mathlib.Logic.Function.Defs
import Batteries.Tactic.Init
import Mathlib.Data.Option.NAry

open Option
open Function
variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  constructor
  · intro h
    cases a <;> cases b <;> try {exfalso; exact h rfl}
    · exact ⟨_, _, mem_some_self _, mem_some_self _, rfl⟩
  · rintro ⟨a', b', ha', hb', rfl⟩
    rcases ha' with ⟨rfl⟩
    rcases hb' with ⟨rfl⟩
    exact mem_some_self (f a' b')
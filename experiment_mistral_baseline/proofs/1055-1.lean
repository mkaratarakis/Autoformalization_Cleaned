import Mathlib.Logic.Function.Defs
import Batteries.Tactic.Init
import Mathlib.Data.Option.NAry

open Option
open Function
variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  unfold map₂
  simp only [bind_eq_some, mem_def.isSome, mem_some_iff]
  constructor
  · rintro ⟨a', b', rfl⟩
    exact ⟨a', b', mem_some_iff.2 rfl, mem_some_iff.2 rfl, rfl⟩
  · rintro ⟨a', b', ha', hb', rfl⟩
    exact ⟨a', b', rfl⟩

/- ACTUAL PROOF OF Option.mem_map₂_iff -/

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂, bind_eq_some]
import Mathlib.Logic.Function.Defs
import Batteries.Tactic.Init
import Mathlib.Data.Option.NAry

open Option
open Function
variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  unfold map₂
  cases a <;> cases b
  · simp
  · simp
  · simp
  · simp [mem_def]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨a, b, rfl, rfl, rfl⟩
    · rintro ⟨a', b', a'_mem, b'_mem, f_eq⟩
      exact ⟨rfl, f_eq.symm⟩

/- ACTUAL PROOF OF Option.mem_map₂_iff -/

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂, bind_eq_some]
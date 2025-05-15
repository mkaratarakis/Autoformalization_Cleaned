import Mathlib.Logic.Function.Defs
import Batteries.Tactic.Init
import Mathlib.Data.Option.NAry

open Option
open Function
variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  constructor
  · intro h
    cases a
    · contradiction
    · cases b
      · contradiction
      · existsi a_val, b_val
        simp [h]
        apply And.intro
        · exact Option.mem_some.mpr rfl
        · exact Option.mem_some.mpr rfl
  · rintro ⟨a', a'_mem, b', b'_mem, rfl⟩
    cases a
    · contradiction
    · cases b
      · contradiction
      · exact Option.mem_some.mpr (Option.mem_map₂_iff.mpr ⟨a', b', a'_mem, b'_mem, rfl⟩)

/- ACTUAL PROOF OF Option.mem_map₂_iff -/

example {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  simp [map₂, bind_eq_some]
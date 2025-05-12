import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Bool.AllAny

open List
variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

example : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  constructor
  · intro h
    obtain ⟨a, hl, hp⟩ := h
    exact ⟨a, hl, hp⟩
  · rintro ⟨a, hl, hp⟩
    exact List.any_iff_exists_prop.2 ⟨a, hl, hp⟩

/- ACTUAL PROOF OF List.any_iff_exists_prop -/

example : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  simp
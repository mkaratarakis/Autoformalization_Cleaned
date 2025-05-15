import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Bool.AllAny

open List
variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

example : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  constructor
  · intro h
    apply Exists.elim (List.any_iff_exists_prop.1 h)
    | intro a hmem
      exact ⟨a, hmem⟩
  · rintro ⟨a, hmem⟩
    exact List.any_iff_exists_prop.2 ⟨a, hmem⟩

/- ACTUAL PROOF OF List.any_iff_exists_prop -/

example : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  simp
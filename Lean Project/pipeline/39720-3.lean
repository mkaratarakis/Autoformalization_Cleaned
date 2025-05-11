import Mathlib.Tactic.TypeStar
import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar

/-!
# Boolean quantifiers

This proves a few properties about `List.all` and `List.any`, which are the `Bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List
example : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp

theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp

theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_eq_true.2 ⟨_, h₁, h₂⟩

end List

theorem List.any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  constructor
  · intro h
    exact Exists.elim (List.any_eq_true.1 h) (fun x => fun hx => ⟨x.1, x.2.1, x.2.2⟩)
  · rintro ⟨a, hmem, hp⟩
    exact List.any_of_mem hmem (by simp [hp])

/- ACTUAL PROOF OF List.any_iff_exists_prop -/

example : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by
  simp
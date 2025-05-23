import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · intro h
    rw [h]
    apply And.intro
    · apply le_refl
    · apply le_refl
  · intro h
    apply le_antisymm
    · exact h.1
    · exact h.2

/- ACTUAL PROOF OF Int.eq_iff_le_and_ge -/

example {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · intro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂
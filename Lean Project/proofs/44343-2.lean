import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · intro h
    rw [h]
    exact ⟨le_of_eq h, le_of_eq h⟩
  · intro h
    exact le_antisymm h.1 h.2

/- ACTUAL PROOF OF Int.eq_iff_le_and_ge -/

example {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · intro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂
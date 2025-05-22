import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · intro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂
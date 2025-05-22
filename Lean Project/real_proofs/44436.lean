import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]
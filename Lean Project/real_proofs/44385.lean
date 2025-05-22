import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    cases Int.lt_trichotomy a b
    case inl lt => exact Or.inl lt
    case inr h =>
      cases h
      case inl =>simp_all
      case inr gt => exact Or.inr gt
  · intro h
    cases h
    case inl lt => exact Int.ne_of_lt lt
    case inr gt => exact Int.ne_of_gt gt
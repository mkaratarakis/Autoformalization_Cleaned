import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card

open Finite
open scoped Classical
variable {α β γ : Type*}


example [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]
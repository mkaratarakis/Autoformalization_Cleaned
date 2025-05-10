import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card

open Nat
open scoped Classical
variable {α β γ : Type*}


example (α : Type*) :
    Nat.card α = if h : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · letI := Fintype.ofFinite α
    simp only [*, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]
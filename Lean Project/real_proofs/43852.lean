import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card

open Finite
open scoped Classical
variable {α β γ : Type*}


example [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
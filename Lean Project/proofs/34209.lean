import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (a : Char) : ¬ a < a := by
  intro h
  have h₁ : a.toNat < a.toNat := h
  exact Nat.lt_irrefl a.toNat h₁

/- ACTUAL PROOF OF Char.lt_irrefl -/

example (a : Char) : ¬ a < a := by
  simp
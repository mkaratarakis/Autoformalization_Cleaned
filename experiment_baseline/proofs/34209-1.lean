import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (a : Char) : ¬ a < a := by
  intro h
  apply toNat.inj
  have h' := toNat.lt_toNat h
  exact Nat.lt_irrefl _ h'

/- ACTUAL PROOF OF Char.lt_irrefl -/

example (a : Char) : ¬ a < a := by
  simp
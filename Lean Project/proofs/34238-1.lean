import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (c : Char) : Char.ofNat c.toNat = c := by
  unfold Char.ofNat
  cases c
  exact rfl

/- ACTUAL PROOF OF Char.ofNat_toNat -/

example (c : Char) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos]
  rfl
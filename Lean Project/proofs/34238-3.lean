import Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import Init.Data.Char.Lemmas

open Char


example (c : Char) : Char.ofNat c.toNat = c := by
  unfold Char.ofNat
  cases c
  simp [Char.ofNatAux]
  split
  · intro h
    simp [UInt32.ofNatLT]
    exact rfl
  · simp [UInt32.ofNatLT]
    apply Char.noConfusion

/- ACTUAL PROOF OF Char.ofNat_toNat -/

example (c : Char) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos]
  rfl
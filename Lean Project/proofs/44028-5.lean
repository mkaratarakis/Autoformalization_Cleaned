import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example : @BitVec.ofFin w (Fin.mk x lt) = BitVec.ofNat w x := by
  simp [BitVec.ofFin, BitVec.ofNat, Fin.mk]
  simp [Fin.ofNat']
  rfl

/- ACTUAL PROOF OF BitVec.ofFin_eq_ofNat -/

example : @BitVec.ofFin w (Fin.mk x lt) = BitVec.ofNat w x := by
  simp only [BitVec.ofNat, Fin.ofNat', lt, Nat.mod_eq_of_lt]
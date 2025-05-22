import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  rw [ofNat, toNat]
  simp [Nat.mod_def]

/- ACTUAL PROOF OF BitVec.toNat_ofNat -/

example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']
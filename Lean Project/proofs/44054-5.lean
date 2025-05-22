import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [ofNat, toNat, Fin.ofNat']
  exact Nat.mod_mod_of_dvd (two_ne_zero w).symm.dvd_pow_two_mod

/- ACTUAL PROOF OF BitVec.toNat_ofNat -/

example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']
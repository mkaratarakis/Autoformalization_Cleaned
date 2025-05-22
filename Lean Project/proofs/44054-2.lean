import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  unfold toNat
  unfold ofNat
  simp
  simp [Nat.mod_def]
  exact Nat.mod_mod_of_dvd (Nat.dvd_of_mod_eq_zero (Nat.mod_eq_of_lt (Nat.pow_pos two_ne_zero _).le))

/- ACTUAL PROOF OF BitVec.toNat_ofNat -/

example (x w : Nat) : (BitVec.ofNat w x).toNat = x % 2^w := by
  simp [BitVec.toNat, BitVec.ofNat, Fin.ofNat']
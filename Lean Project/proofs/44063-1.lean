import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) (y : Nat)
  : (y = x.toNat) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  constructor
  · intro h
    rw [h]
    apply toNat_ofNat_lt_pow
  · intro h
    rw [(toNat_ofNat h.2.symm)]

/- ACTUAL PROOF OF BitVec.nat_eq_toNat -/

example (x : BitVec w) (y : Nat)
  : (y = x.toNat) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  rw [@eq_comm _ _ x.toNat]
  apply toNat_eq_nat
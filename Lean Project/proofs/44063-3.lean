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
    exact ⟨BitVec.toNat_lt_two_pow x, rfl⟩
  · rintro ⟨hy, rfl⟩
    exact BitVec.ofNat_toNat hy

/- ACTUAL PROOF OF BitVec.nat_eq_toNat -/

example (x : BitVec w) (y : Nat)
  : (y = x.toNat) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  rw [@eq_comm _ _ x.toNat]
  apply toNat_eq_nat
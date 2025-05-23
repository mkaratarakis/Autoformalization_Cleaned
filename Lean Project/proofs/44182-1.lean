import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Nat) : (BitVec.ofNat n x) ≤ (BitVec.ofNat n y) ↔ x % 2^n ≤ y % 2^n := by
  constructor
  · intro h
    rw [← Nat.mod_eq_of_lt (Nat.lt_pow_succ_of_pos _ _)]
    rw [← Nat.mod_eq_of_lt (Nat.lt_pow_succ_of_pos _ _)]
    exact h
  · intro h
    rw [← Nat.mod_eq_of_lt (Nat.lt_pow_succ_of_pos _ _)]
    rw [← Nat.mod_eq_of_lt (Nat.lt_pow_succ_of_pos _ _)]
    exact h

/- ACTUAL PROOF OF BitVec.ofNat_le_ofNat -/

example {n} (x y : Nat) : (BitVec.ofNat n x) ≤ (BitVec.ofNat n y) ↔ x % 2^n ≤ y % 2^n := by
  simp [le_def]
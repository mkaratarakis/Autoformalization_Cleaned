import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Nat) : BitVec.ofNat n x < BitVec.ofNat n y ↔ x % 2^n < y % 2^n := by
  constructor
  · intro h
    exact Nat.mod_lt_of_lt (BitVec.val_lt_iff.mp h) (Nat.zero_lt_pow 2 n)
  · intro h
    exact BitVec.val_lt_iff.mpr (Nat.lt_of_mod_lt h (Nat.zero_lt_pow 2 n))

/- ACTUAL PROOF OF BitVec.ofNat_lt_ofNat -/

example {n} (x y : Nat) : BitVec.ofNat n x < BitVec.ofNat n y ↔ x % 2^n < y % 2^n := by
  simp [lt_def]
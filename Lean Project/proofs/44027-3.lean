import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec n) : x ≠ y ↔ x.toNat ≠ y.toNat := by
  constructor
  · intro h
    apply Ne.symm
    rw [← ofInt_eq_toNat]
    apply Ne.symm
    exact h
  · intro h
    apply Ne.symm
    rw [← ofInt_eq_toNat]
    exact h

/- ACTUAL PROOF OF BitVec.toNat_ne -/

example (x y : BitVec n) : x ≠ y ↔ x.toNat ≠ y.toNat := by
  rw [Ne, toNat_eq]
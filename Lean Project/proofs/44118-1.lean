import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w₁} {y : BitVec w₂} : x <<< y = x <<< y.toNat := by
  rw [toNat_eq_val]
  exact (shl_val_eq_shl_toNat x y).symm

/- ACTUAL PROOF OF BitVec.shiftLeft_eq' -/

example {x : BitVec w₁} {y : BitVec w₂} : x <<< y = x <<< y.toNat := by
  rfl
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w₁} {y : BitVec w₂} {z : BitVec w₃} :
    x <<< y <<< z = x <<< (y.toNat + z.toNat) := by
  simp [shll, toNat]
  rw [Nat.add_assoc]
  rfl

/- ACTUAL PROOF OF BitVec.shiftLeft_shiftLeft' -/

example {x : BitVec w₁} {y : BitVec w₂} {z : BitVec w₃} :
    x <<< y <<< z = x <<< (y.toNat + z.toNat) := by
  simp [shiftLeft_add]
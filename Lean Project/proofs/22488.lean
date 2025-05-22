import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x : BitVec w₁} {y : BitVec w₂} :
    shiftLeftRec x y 0 = x <<< (y &&& twoPow w₂ 0) := by
  rw [shiftLeftRec, twoPow]
  simp
  rfl

/- ACTUAL PROOF OF BitVec.shiftLeftRec_zero -/

example {x : BitVec w₁} {y : BitVec w₂} :
    shiftLeftRec x y 0 = x <<< (y &&& twoPow w₂ 0) := by
  simp [shiftLeftRec]
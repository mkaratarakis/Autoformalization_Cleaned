import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x : BitVec w₁) (y : BitVec w₂) :
    x <<< y = shiftLeftRec x y (w₂ - 1) := by
  cases w₂
  · simp [shiftLeftRec]
  · have : (n + 1) - 1 = n := by rfl
    simp [shiftLeftRec, this, BitVec.shl, BitVec.zeroExtend, BitVec.truncate]

/- ACTUAL PROOF OF BitVec.shiftLeft_eq_shiftLeftRec -/

example (x : BitVec w₁) (y : BitVec w₂) :
    x <<< y = shiftLeftRec x y (w₂ - 1) := by
  rcases w₂ with rfl | w₂
  · simp [of_length_zero]
  · simp [shiftLeftRec_eq]
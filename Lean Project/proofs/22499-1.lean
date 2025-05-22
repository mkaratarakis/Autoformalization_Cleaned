import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y (n + 1) = (ushiftRightRec x y n) >>> (y &&& twoPow w₂ (n + 1)) := by
  rw [ushiftRightRec]
  rw [BitVec.ushiftRightRec]
  rw [BitVec.ushiftRightRec]
  rw [BitVec.twoPow]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
  rw [BitVec.ushiftRight]
 

/- ACTUAL PROOF OF BitVec.ushiftRightRec_succ -/

example (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y (n + 1) = (ushiftRightRec x y n) >>> (y &&& twoPow w₂ (n + 1)) := by
  simp [ushiftRightRec]
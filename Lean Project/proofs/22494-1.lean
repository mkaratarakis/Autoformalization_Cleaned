import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y 0 = x >>> (y &&& twoPow w₂ 0) := by
  unfold ushiftRightRec
  rw [Nat.Mod.mod, Nat.Mod.mod_self]
  rw [Bitblast.ushiftRightRec]
  rw [Bitblast.twoPow]
  rw [Bitblast.and]
  rw [Bitblast.shiftr]
  rw [Bitblast.ushiftRightRec]
  rw [Bitblast.twoPow]
  rw [Bitblast.and]
  rw [Bitblast.shiftr]

/- ACTUAL PROOF OF BitVec.ushiftRightRec_zero -/

example (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y 0 = x >>> (y &&& twoPow w₂ 0) := by
  simp [ushiftRightRec]
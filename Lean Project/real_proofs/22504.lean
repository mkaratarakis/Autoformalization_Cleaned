import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool


example {x : BitVec w₁} {y : BitVec w₂} :
    shiftLeftRec x y (n + 1) = (shiftLeftRec x y n) <<< (y &&& twoPow w₂ (n + 1)) := by
  simp [shiftLeftRec]
import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool


example {x y : BitVec w} :
    carry w x y c = decide (x.toNat + y.toNat + c.toNat ≥ 2^w) := by
  simp [carry]
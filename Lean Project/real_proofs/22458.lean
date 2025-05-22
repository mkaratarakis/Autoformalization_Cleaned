import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool


example : atLeastTwo a b false = (a && b) := by
  simp [atLeastTwo]
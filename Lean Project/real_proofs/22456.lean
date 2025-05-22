import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool


example : atLeastTwo false b c = (b && c) := by
  simp [atLeastTwo]
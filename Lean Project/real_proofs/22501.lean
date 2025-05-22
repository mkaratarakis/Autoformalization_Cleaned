import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool


example : atLeastTwo a true c  = (a || c) := by
  cases a <;> cases c <;> simp [atLeastTwo]
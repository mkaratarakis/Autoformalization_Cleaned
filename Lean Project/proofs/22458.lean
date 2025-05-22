import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo a b false = (a && b) := by
  unfold atLeastTwo
  simp [Bool.and_false, Bool.or_self]
  simp [Bool.and_false, Bool.or_false_left]

/- ACTUAL PROOF OF Bool.atLeastTwo_false_right -/

example : atLeastTwo a b false = (a && b) := by
  simp [atLeastTwo]
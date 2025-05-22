import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo a b false = (a && b) := by
  unfold atLeastTwo
  simp [and_false, or_self]

/- ACTUAL PROOF OF Bool.atLeastTwo_false_right -/

example : atLeastTwo a b false = (a && b) := by
  simp [atLeastTwo]
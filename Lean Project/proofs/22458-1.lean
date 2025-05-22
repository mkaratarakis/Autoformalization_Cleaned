import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo a b false = (a && b) := by
  unfold atLeastTwo
  unfold ite
  split
  case tt =>
    split
    case tt =>
      rfl
    case ff =>
      simp
  case ff =>
    split
    case tt =>
      simp
    case ff =>
      simp

/- ACTUAL PROOF OF Bool.atLeastTwo_false_right -/

example : atLeastTwo a b false = (a && b) := by
  simp [atLeastTwo]
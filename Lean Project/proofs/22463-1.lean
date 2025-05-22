import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo a false c = (a && c) := by
  unfold atLeastTwo
  simp
  by_cases h : a = true;
  · simp [h]
  · simp [h]

/- ACTUAL PROOF OF Bool.atLeastTwo_false_mid -/

example : atLeastTwo a false c = (a && c) := by
  simp [atLeastTwo]
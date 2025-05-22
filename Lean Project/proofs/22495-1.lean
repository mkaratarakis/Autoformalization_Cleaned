import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo a b true  = (a || b) := by
  cases a <;> cases b
  · simp [atLeastTwo]
  · simp [atLeastTwo]
  · simp [atLeastTwo]
  · simp [atLeastTwo]

/- ACTUAL PROOF OF Bool.atLeastTwo_true_right -/

example : atLeastTwo a b true  = (a || b) := by
  cases a <;> cases b <;> simp [atLeastTwo]
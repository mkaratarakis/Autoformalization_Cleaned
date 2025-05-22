import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open Bool
open Nat Bool

example : atLeastTwo false b c = (b && c) := by
  unfold atLeastTwo
  rw false_and
  simp

/- ACTUAL PROOF OF Bool.atLeastTwo_false_left -/

example : atLeastTwo false b c = (b && c) := by
  simp [atLeastTwo]
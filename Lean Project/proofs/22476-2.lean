import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.ule y = !y.ult x := by
  unfold ult
  rw [← not_iff_not_of_bool_eq_eq]
  unfold ule
  rfl

/- ACTUAL PROOF OF BitVec.ule_eq_not_ult -/

example (x y : BitVec w) : x.ule y = !y.ult x := by
  simp [BitVec.ule, BitVec.ult, ← decide_not]
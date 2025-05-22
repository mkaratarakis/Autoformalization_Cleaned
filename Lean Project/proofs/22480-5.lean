import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.sle y = !y.slt x := by
  unfold BitVec.sle BitVec.slt
  rw [←not_iff_not, ←bool_eq_dec, ←bool_not_dec]
  simp [decide_eq_true_iff, decide_eq_false_iff]
  rw [← not_le]
  omega

/- ACTUAL PROOF OF BitVec.sle_eq_not_slt -/

example (x y : BitVec w) : x.sle y = !y.slt x := by
  simp only [BitVec.sle, BitVec.slt, ← decide_not, decide_eq_decide]; omega
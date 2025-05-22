import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x : BitVec w) : allOnes w - x = ~~~x := by
  rw [← add_bv_assoc, ← Nat.sub_add_cancel, add_bv_comm]
  rfl

/- ACTUAL PROOF OF BitVec.allOnes_sub_eq_not -/

example (x : BitVec w) : allOnes w - x = ~~~x := by
  rw [← add_not_self x, BitVec.add_comm, add_sub_cancel]
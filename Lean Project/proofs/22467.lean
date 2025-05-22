import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} :
    carry w x y c = decide (x.toNat + y.toNat + c.toNat ≥ 2^w) := by
  unfold carry
  simp [decide_eq_true_iff]
  rw [Nat.add_lt_add_iff_right]
  rw [Nat.add_lt_add_iff_right]
  rw [Nat.add_lt_add_iff_right]
  exact Nat.lt_pow2_iff_bodd w (x.toNat + y.toNat + c.toNat)

/- ACTUAL PROOF OF BitVec.carry_width -/

example {x y : BitVec w} :
    carry w x y c = decide (x.toNat + y.toNat + c.toNat ≥ 2^w) := by
  simp [carry]
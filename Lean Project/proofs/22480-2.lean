import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x y : BitVec w) : x.sle y = !y.slt x := by
  simp_all only [sle, slt, bvult, bvule, not_eq_ff, bv2nat, bvshl, bvshr, bvand, bvor, bvxor, bvneg, bvadd, bvsub, bvmul, bvudiv, bvurem, bvshl, bvshr, bv2nat_eq, bv2nat_lt, bv2nat_le, bv2nat_div, bv2nat_mod, bv2nat_shl, bv2nat_shr]
  rw [←not_iff_not, ←bool_eq_dec, ←bool_not_dec]
  omega

/- ACTUAL PROOF OF BitVec.sle_eq_not_slt -/

example (x y : BitVec w) : x.sle y = !y.slt x := by
  simp only [BitVec.sle, BitVec.slt, ← decide_not, decide_eq_decide]; omega
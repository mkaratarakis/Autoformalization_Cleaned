import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool


example (x y : BitVec w) :
    x.slt y = (x.msb == y.msb).xor (carry w x (~~~y) true) := by
  simp only [slt_eq_ult, bne, ult_eq_not_carry]
  cases x.msb == y.msb <;> simp
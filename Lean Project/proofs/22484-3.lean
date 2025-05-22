import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example : carry 0 x y c = c := by
  cases c <;>
    simp [carry]
    simp [Nat.ModEq, Nat.mod_one]
    constructor <;>
      apply Nat.mod_lt <;>
      simp

/- ACTUAL PROOF OF BitVec.carry_zero -/

example : carry 0 x y c = c := by
  cases c <;> simp [carry, mod_one]
import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool


example : carry 0 x y c = c := by
  cases c <;> simp [carry, mod_one]
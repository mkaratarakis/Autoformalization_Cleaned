import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc, ofBool, zeroExtend]
  simp [adcb, iunfoldr]
  rfl

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
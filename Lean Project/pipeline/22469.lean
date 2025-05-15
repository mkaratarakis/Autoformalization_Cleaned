import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  have : adc x y false = (carry w x y false, x + y + zeroExtend w (ofBool false)) := by
    apply adc_spec
  rw [this]
  simp [ofBool, zeroExtend]
  rw [add_zero]

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
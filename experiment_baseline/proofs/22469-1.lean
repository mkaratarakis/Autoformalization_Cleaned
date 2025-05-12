import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  have h : adc x y false = (carry w x y false, x + y + zeroExtend w (ofBool false)) := by
    exact adc_spec w x y false
  rw [h]
  have h' : zeroExtend w (ofBool false) = 0 := by
    simp [zeroExtend, ofBool]
  rw [h']
  simp

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
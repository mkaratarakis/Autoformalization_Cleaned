import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  rw [←add_eq_adc]
  simp
  exact (adc_false_carry x y).snd
example (x y : BitVec w) : adc x y false = (carry w x y false, x + y) := by
  apply adc_spec
  simp [ofBool_false, zeroExtend_zero]

theorem add_eq_adc (x y : BitVec w) : x + y = (adc x y false).snd := by
  rw [adc_false_carry]
  exact rfl

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
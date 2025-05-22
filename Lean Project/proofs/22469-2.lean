import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  rw [← ofBool_zero_eq_false]
  rw [adc_eq_carry_sum]
  rw [Bool.ofNat_zero]
  rw [zeroExtend_zero]
  rw [zero_add]

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
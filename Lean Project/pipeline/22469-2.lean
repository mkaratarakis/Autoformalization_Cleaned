import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  have h : iunfoldr (fun i c => adcb x[↑i] y[↑i] c) false = (carry w x y false, x + y) := by
    apply iunfoldr_replace
    · exact fun i => carryRec w x y false i
    · exact x + y
    · exact false
    · simp
    · intro i
      simp [carryRec]

/- ACTUAL PROOF OF BitVec.add_eq_adc -/

example (w : Nat) (x y : BitVec w) : x + y = (adc x y false).snd := by
  simp [adc_spec]
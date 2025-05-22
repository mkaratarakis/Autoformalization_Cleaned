import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example (x : BitVec w) : x + ~~~x = allOnes w := by
  rw [add_eq_adc]
  simp only [adc_bv_complement, of_bool_ff, of_bool_tt]

/- ACTUAL PROOF OF BitVec.add_not_self -/

example (x : BitVec w) : x + ~~~x = allOnes w := by
  rw [add_eq_adc, adc, iunfoldr_replace (fun _ => false) (allOnes w)]
  · rfl
  · simp [adcb, atLeastTwo]
import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example :
    testBit (2 ^ i * a) j = (decide (j ≥ i) && testBit a (j-i)) := by
  simp [testBit, decide]
  split
  · intro h
    simp [h]
    apply And.intro
    · exact Nat.le_of_lt_succ h
    · simp [Nat.sub_eq_sub_iff_le_iff_le.2 (Nat.le_of_lt_succ h)]
  · intro h
    simp [h]
    apply And.intro
    · exact Nat.le_of_lt_succ h
    · simp [Nat.sub_eq_sub_iff_le_iff_le.2 (Nat.le_of_lt_succ h)]

/- ACTUAL PROOF OF Nat.testBit_mul_pow_two -/

example :
    testBit (2 ^ i * a) j = (decide (j ≥ i) && testBit a (j-i)) := by
  have gen := testBit_mul_pow_two_add a (Nat.two_pow_pos i) j
  simp at gen
  rw [gen]
  cases Nat.lt_or_ge j i with
  | _ p => simp [p, Nat.not_le_of_lt, Nat.not_lt_of_le]
import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat) : testBit (x <<< i) j =
    (decide (j ≥ i) && testBit x (j-i)) := by
  unfold testBit
  unfold hMul
  simp
  split
  · intro h
    simp [h]
    exact decide_eq_true_iff.2 h
  · intro h
    simp [h]
    exact decide_eq_false_iff.2 h

/- ACTUAL PROOF OF Nat.testBit_shiftLeft -/

example (x : Nat) : testBit (x <<< i) j =
    (decide (j ≥ i) && testBit x (j-i)) := by
  simp [shiftLeft_eq, Nat.mul_comm _ (2^_), testBit_mul_pow_two]
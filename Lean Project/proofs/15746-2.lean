import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x i : Nat) : testBit x (succ i) = testBit (x/2) i := by
  unfold testBit
  simp [land_eq_one_iff]
  rw [shiftr_def]
  simp [land_eq_one_iff, shiftr_def]
  rw [shiftr_succ_eq_div]

/- ACTUAL PROOF OF Nat.testBit_succ -/

example (x i : Nat) : testBit x (succ i) = testBit (x/2) i := by
  unfold testBit
  simp [shiftRight_succ_inside]
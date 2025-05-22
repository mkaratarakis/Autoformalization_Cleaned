import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example : testBit 1 0 = true := by
  unfold testBit
  simp

/- ACTUAL PROOF OF Nat.testBit_one_zero -/

example : testBit 1 0 = true := by
  trivial
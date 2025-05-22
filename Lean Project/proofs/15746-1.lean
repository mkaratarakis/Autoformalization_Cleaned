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
  simp [Nat.land, Nat.shiftr]
  rw [Nat.div_two_eq_shiftr]
  simp [Nat.land, Nat.shiftr]

/- ACTUAL PROOF OF Nat.testBit_succ -/

example (x i : Nat) : testBit x (succ i) = testBit (x/2) i := by
  unfold testBit
  simp [shiftRight_succ_inside]
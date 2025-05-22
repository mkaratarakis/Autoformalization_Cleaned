import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x i : Nat) : testBit x (i + 1) = testBit (x/2) i := by
  unfold testBit
  simp
  rw [shiftr_succ]
  rw [Nat.div2_eq_shiftr]
  rfl

/- ACTUAL PROOF OF Nat.testBit_add_one -/

example (x i : Nat) : testBit x (i + 1) = testBit (x/2) i := by
  unfold testBit
  simp [shiftRight_succ_inside]
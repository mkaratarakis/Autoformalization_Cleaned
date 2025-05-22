import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (i : Nat) : testBit 0 i = false := by
  rw [testBit]
  simp [Nat.shiftRight, Nat.land, beq_iff_eq, Bool.beq_iff_eq_dec]
  rfl

/- ACTUAL PROOF OF Nat.zero_testBit -/

example (i : Nat) : testBit 0 i = false := by
  simp only [testBit, zero_shiftRight, and_zero, bne_self_eq_false]
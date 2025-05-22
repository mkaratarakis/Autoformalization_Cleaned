import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (n i : Nat) : testBit (2^n-1) i = decide (i < n) := by
  rw [← Nat.sub_add_cancel (zero_lt_pow_two n)]
  simp [Nat.testBit_sub_one, zero_testBit]

/- ACTUAL PROOF OF Nat.testBit_two_pow_sub_one -/

example (n i : Nat) : testBit (2^n-1) i = decide (i < n) := by
  rw [testBit_two_pow_sub_succ]
  · simp
  · exact Nat.two_pow_pos _
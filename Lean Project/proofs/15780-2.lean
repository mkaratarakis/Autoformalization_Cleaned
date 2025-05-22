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
  have h₁ : 2 ^ n - 1 = 2 ^ n - (0 + 1) := by rfl
  rw [h₁]
  have h₂ : 0 < 2 ^ n := pow_pos zero_lt_succ 1 n
  rw [testBit_sub_pow h₂]
  simp [zero_testBit]

/- ACTUAL PROOF OF Nat.testBit_two_pow_sub_one -/

example (n i : Nat) : testBit (2^n-1) i = decide (i < n) := by
  rw [testBit_two_pow_sub_succ]
  · simp
  · exact Nat.two_pow_pos _
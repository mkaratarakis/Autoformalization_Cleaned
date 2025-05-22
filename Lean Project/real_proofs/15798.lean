import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat



example (x : Nat) {y n : Nat} (right : y < 2^n) : (x &&& y) < 2^n := by
  apply lt_pow_two_of_testBit
  intro i i_ge_n
  have yf : testBit y i = false := by
          apply Nat.testBit_lt_two_pow
          apply Nat.lt_of_lt_of_le right
          exact pow_le_pow_of_le_right Nat.zero_lt_two i_ge_n
  simp [testBit_and, yf]
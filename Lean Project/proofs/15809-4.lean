import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x n : Nat) : x &&& (2^n-1) = x % 2^n := by
  funext i
  by_cases h : i < n
  · have hi : (2^n-1).testBit i := by
      simp
      apply testBit_one_lt
      simp [h]
    calc
      (x &&& 2^n-1).testBit i = x.testBit i && hi := by simp
      _ = x.testBit i := by simp

  · have hi : ¬(2^n-1).testBit i := by
      simp
      apply testBit_zero_of_ge
      simp [h]
    calc
      (x &&& 2^n-1).testBit i = x.testBit i && hi := by simp
      _ = false := by simp
      _ = (x % 2^n).testBit i := by
        simp
        rw [mod_eq_sub_mult_div x 2 n]
        apply testBit_zero_of_ge
        rw [div_eq_of_lt (pow_pos (zero_lt_two) n)]
        simp [h]

/- ACTUAL PROOF OF Nat.and_pow_two_is_mod -/

example (x n : Nat) : x &&& (2^n-1) = x % 2^n := by
  apply eq_of_testBit_eq
  intro i
  simp only [testBit_and, testBit_mod_two_pow]
  cases testBit x i <;> simp
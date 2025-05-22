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
  apply testBit_ext
  intro i
  by_cases h : i < n
  · simp [h, testBit_and, testBit_mod, testBit_pow, testBit_sub]
  · simp [h, testBit_and, testBit_mod, testBit_pow, testBit_sub]
    split
    · intro hx
      apply Nat.not_lt
      exact h
      exact Nat.le_of_testBit hx
    · intro hx
      apply Nat.not_lt
      exact h
      exact Nat.le_of_testBit hx

/- ACTUAL PROOF OF Nat.and_pow_two_is_mod -/

example (x n : Nat) : x &&& (2^n-1) = x % 2^n := by
  apply eq_of_testBit_eq
  intro i
  simp only [testBit_and, testBit_mod_two_pow]
  cases testBit x i <;> simp
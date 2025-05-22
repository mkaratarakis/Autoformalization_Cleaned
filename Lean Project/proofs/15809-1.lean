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
  have h1 : (x &&& (2^n-1)) testBit i = decide (i < n) &&& x testBit i := by
    simp [testBit, Nat.land_def, Nat.ofDigits_bin, ofDigits_testBit,
          ← Nat.pow_eq_two_mul, Nat.sub_eq_add_neg, Nat.mod_eq_of_lt]
    rw [Nat.mod_eq_of_lt (Nat.lt_pow_self 2 n)]
    simp [Nat.ofDigits_bin, ofDigits_testBit, Nat.land_def]
    rw [← Nat.pow_eq_two_mul, Nat.sub_eq_add_neg, Nat.mod_eq_of_lt]
    simp
  have h2 : (x % 2^n) testBit i = decide (i < n) &&& x testBit i := by
    simp [testBit, Nat.mod_def, Nat.ofDigits_bin, ofDigits_testBit,
          ← Nat.pow_eq_two_mul, Nat.sub_eq_add_neg, Nat.mod_eq_of_lt]
    rw [Nat.mod_eq_of_lt (Nat.lt_pow_self 2 n)]
    simp [Nat.ofDigits_bin, ofDigits_testBit, Nat.land_def]
    rw [← Nat.pow_eq_two_mul, Nat.sub_eq_add_neg, Nat.mod_eq_of_lt]
    simp
  rw [h1, h2]
  simp

/- ACTUAL PROOF OF Nat.and_pow_two_is_mod -/

example (x n : Nat) : x &&& (2^n-1) = x % 2^n := by
  apply eq_of_testBit_eq
  intro i
  simp only [testBit_and, testBit_mod_two_pow]
  cases testBit x i <;> simp
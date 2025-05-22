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
  have : ∀ i, i ≥ n → testBit y i = false := by
    intro i h
    have : y < 2^i := by
      apply lt_trans _ (pow_le_pow_of_le 2 (Nat.le_of_lt_succ h))
      exact right
    apply testBit_eq_zero_of_lt_pow this
  intro i h
  apply testBit_eq_zero_of_lt_pow
  apply lt_of_eq_of_lt
  rw [testBit_and]
  rw [this i h]
  rw [false_and]
  exact false_eq_zero
  all_goals
    exact Nat.lt_succ_self n

/- ACTUAL PROOF OF Nat.and_lt_two_pow -/

example (x : Nat) {y n : Nat} (right : y < 2^n) : (x &&& y) < 2^n := by
  apply lt_pow_two_of_testBit
  intro i i_ge_n
  have yf : testBit y i = false := by
          apply Nat.testBit_lt_two_pow
          apply Nat.lt_of_lt_of_le right
          exact pow_le_pow_of_le_right Nat.zero_lt_two i_ge_n
  simp [testBit_and, yf]
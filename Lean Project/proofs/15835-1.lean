import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (a : Nat) {b i : Nat} (b_lt : b < 2^i) (j : Nat) :
    testBit (2 ^ i * a + b) j =
      if j < i then
        testBit b j
      else
        testBit a (j - i) := by
  cases h : j < i
  · -- Case j < i
    simp_arith [testBit, Nat.mul_add, Nat.mul_div_cancel_left]
    rw [Nat.div_eq_of_lt]
    · apply Nat.div_lt_of_lt_mul
      · exact b_lt
      · rw [Nat.mul_one]
      · exact Nat.le_of_lt_succ b_lt
    · exact h
  · -- Case j ≥ i
    rw [Nat.sub_add_cancel]
    · rw [Nat.pow_sub_cancel] at b_lt
      simp_arith [testBit, Nat.mul_add, Nat.mul_div_cancel_left]
      rw [Nat.div_eq_of_lt]
      · apply Nat.div_lt_of_lt_mul
        · exact b_lt
        · rw [Nat.mul_one]
        · exact Nat.le_of_lt_succ b_lt
      · exact h
    · rw [Nat.sub_add_cancel]
      exact h

/- ACTUAL PROOF OF Nat.testBit_mul_pow_two_add -/

example (a : Nat) {b i : Nat} (b_lt : b < 2^i) (j : Nat) :
    testBit (2 ^ i * a + b) j =
      if j < i then
        testBit b j
      else
        testBit a (j - i) := by
  cases Nat.lt_or_ge j i with
  | inl j_lt =>
    simp only [j_lt]
    have i_def : i = j + succ (pred (i-j)) := by
      rw [succ_pred_eq_of_pos] <;> omega
    rw [i_def]
    simp only [testBit_to_div_mod, Nat.pow_add, Nat.mul_assoc]
    simp only [Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_mod]
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc, Nat.mul_add_mod]
  | inr j_ge =>
    have j_def : j = i + (j-i) := (Nat.add_sub_cancel' j_ge).symm
    simp only [
        testBit_to_div_mod,
        Nat.not_lt_of_le,
        j_ge,
        ite_false]
    simp [congrArg (2^·) j_def, Nat.pow_add,
          ←Nat.div_div_eq_div_mul,
          Nat.mul_add_div,
          Nat.div_eq_of_lt b_lt,
          Nat.two_pow_pos i]
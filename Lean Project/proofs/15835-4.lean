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
  cases h : decide (j < i)
  · -- Case j < i
    simp [h, testBit]
    have : (2 ^ i * a + b) % 2 ^ (j + 1) = (b % 2 ^ (j + 1)) := by
      rw [← Nat.mod_add_div (2 ^ i * a) b]
      have : 2 ^ i * a % 2 ^ (j + 1) = 0 := by
        rw [← Nat.mul_mod_left]
        apply Nat.mod_eq_of_lt
        simp
        apply Nat.pow_lt_pow_left (Nat.zero_le _) (Nat.lt_of_lt_succ h)
      rw [this, zero_add]
    rw [this]
    simp [testBit]
  · -- Case j ≥ i
    simp [h, testBit]
    have : (2 ^ i * a + b) % 2 ^ (j + 1) = (2 ^ i * (a % 2 ^ (j - i + 1)) + b % 2 ^ (j + 1)) := by
      rw [← Nat.mod_add_div (2 ^ i * a) b, Nat.mod_eq_of_lt]
      · apply Nat.pow_lt_pow_left (Nat.zero_le _)
        rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
        exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
      · rw [← Nat.mul_mod_left, Nat.mod_eq_of_lt]
        apply Nat.pow_lt_pow_left (Nat.zero_le _)
        rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
        exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    rw [this, Nat.mul_mod_right, Nat.add_mod_right_of_dvd]
    · exact fun x y => Nat.dvd_pow (Nat.dvd_refl x) y
    · rw [Nat.mul_mod, Nat.mod_eq_of_lt]
      apply Nat.pow_lt_pow_left (Nat.zero_le _)
      rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
      exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    · rw [Nat.mod_eq_of_lt]
      apply Nat.pow_lt_pow_left (Nat.zero_le _)
      rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
      exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
    simp [testBit, Nat.land_eq_and, Bool.ofDecide_eq_eq]
    congr 1
    · have : j - i + 1 > 0 := by
        rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
        exact Nat.succ_pos _
      rw [Nat.mod_eq_of_lt]
      · exact this
      · apply Nat.pow_lt_pow_left (Nat.zero_le _)
        rw [Nat.sub_add_cancel (Nat.le_of_not_lt h)]
        exact Nat.lt_succ_of_le (Nat.le_add_right _ _)

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
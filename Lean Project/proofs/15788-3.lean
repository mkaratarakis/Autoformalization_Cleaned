import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {i j : Nat} (j_lt_i : j < i) (x : Nat) :
    testBit (2^i + x) j = testBit x j := by
  have h : i = j + (i - j) := by
    exact (add_sub_cancel i j).symm
  rw [h]
  simp [testBit, pow_add, add_comm, Nat.div_add_mod]
  cases h' : (i - j) with
  | zero =>
    intro h1
    exfalso
    exact not_le_of_lt j_lt_i (Nat.sub_eq_zero_of_le h1)
  | succ d =>
    simp [pow_succ, mul_comm, Nat.mod_add_div]
  rfl

/- ACTUAL PROOF OF Nat.testBit_two_pow_add_gt -/

example {i j : Nat} (j_lt_i : j < i) (x : Nat) :
    testBit (2^i + x) j = testBit x j := by
  have i_def : i = j + (i-j) := (Nat.add_sub_cancel' (Nat.le_of_lt j_lt_i)).symm
  rw [i_def]
  simp only [testBit_to_div_mod, Nat.pow_add,
        Nat.add_comm x, Nat.mul_add_div (Nat.two_pow_pos _)]
  match i_sub_j_eq : i - j with
  | 0 =>
    exfalso
    rw [Nat.sub_eq_zero_iff_le] at i_sub_j_eq
    exact Nat.not_le_of_gt j_lt_i i_sub_j_eq
  | d+1 =>
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_add_mod]
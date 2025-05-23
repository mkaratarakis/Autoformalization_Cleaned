import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (w : Nat) (i : Nat) : (twoPow w i).toNat = 2^i % 2^w := by
  cases w with
  | zero =>
    simp [twoPow]
    rw [Nat.mod_one]
  | succ w' =>
    simp [twoPow]
    have h1 : 1 < 2 ^ (w' + 1) := by
      apply Nat.one_lt_pow
      exact Nat.zero_lt_succ w'
    rw [Nat.mod_eq_of_lt h1]
    rw [BitVec.shiftLeft_eq_mul_pow]
    rw [Nat.mul_mod]

/- ACTUAL PROOF OF BitVec.toNat_twoPow -/

example (w : Nat) (i : Nat) : (twoPow w i).toNat = 2^i % 2^w := by
  rcases w with rfl | w
  · simp [Nat.mod_one]
  · simp only [twoPow, toNat_shiftLeft, toNat_ofNat]
    have h1 : 1 < 2 ^ (w + 1) := Nat.one_lt_two_pow (by omega)
    rw [Nat.mod_eq_of_lt h1, Nat.shiftLeft_eq, Nat.one_mul]
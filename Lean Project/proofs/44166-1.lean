import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  have : (2^n - x.toNat) % 2^n = 2^n - x.toNat := by
    apply Nat.mod_eq_of_lt
    apply Nat.sub_lt_left_of_pos
    exact Nat.pos_of_ne_zero (by simp)
  simp [toNat_neg, this]

/- ACTUAL PROOF OF BitVec.toNat_neg -/

example (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]
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
    have : x.toNat < 2^n
    . apply toNat_lt_pow
    . exact Nat.zero_lt_of_ne_zero (by simp)
  simp [toNat_neg, this]

/- ACTUAL PROOF OF BitVec.toNat_neg -/

example (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]
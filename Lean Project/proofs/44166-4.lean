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
    have : x.toNat < 2^n := toNat_lt_two_pow n x
    exact Nat.sub_lt (pow_pos two_ne_zero _) this
  simp [toNat_neg, this]

/- ACTUAL PROOF OF BitVec.toNat_neg -/

example (x : BitVec n) : (- x).toNat = (2^n - x.toNat) % 2^n := by
  simp [Neg.neg, BitVec.neg]
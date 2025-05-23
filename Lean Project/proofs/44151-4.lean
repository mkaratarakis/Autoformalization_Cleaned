import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : BitVec n) : x - y = .ofNat n ((2^n - y.toNat) + x.toNat) := by
  simp [sub_eq_add_neg, BitVec.ofNat_eq_iff, Nat.mod_eq_of_lt, BitVec.toNat_eq_iff, Nat.sub_eq_add_neg]
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.add_mod]
  simp

/- ACTUAL PROOF OF BitVec.sub_def -/

example {n} (x y : BitVec n) : x - y = .ofNat n ((2^n - y.toNat) + x.toNat) := by
  rfl
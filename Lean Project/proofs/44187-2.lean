import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : BitVec n) : x - y = x + - y := by
  have h1 : (x - y).toNat = (x + (-y)).toNat := by
    simp [toNat_sub, toNat_add, toNat_neg]
    rw [Nat.add_comm, Nat.add_assoc]
    apply Nat.mod_eq_of_eq
    rw [Nat.add_comm, ←Nat.sub_add_cancel (le_of_lt (pow_lt_pow_right two_pos n y.toNat))]
    exact (Nat.mod_eq_of_lt (pow_lt_pow_right two_pos n y.toNat)).symm
  exact BitVec.eq_of_toNat_eq h1

/- ACTUAL PROOF OF BitVec.sub_toAdd -/

example {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp
  rw [Nat.add_comm]
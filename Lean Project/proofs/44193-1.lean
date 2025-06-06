import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Nat) : BitVec.ofNat n x - BitVec.ofNat n y = .ofNat n ((2^n - y % 2^n) + x) := by
  have : toNat (BitVec.ofNat n x - BitVec.ofNat n y) = toNat (BitVec.ofNat n ((2^n - y % 2^n) + x)) := by
  rw [toNat_sub]
  rw [toNat_ofNat]
  rw [Nat.ModEq]
  rw [Nat.sub_eq_add_neg]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
  rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact Nat.pow_pos dec_trivial
 

/- ACTUAL PROOF OF BitVec.ofNat_sub_ofNat -/

example {n} (x y : Nat) : BitVec.ofNat n x - BitVec.ofNat n y = .ofNat n ((2^n - y % 2^n) + x) := by
  apply eq_of_toNat_eq ; simp [BitVec.ofNat]
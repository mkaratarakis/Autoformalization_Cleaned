import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec n) : x - x = 0#n := by
  -- It suffices to show that (x - x).toNat = (0#n).toNat
  have h1 : (x - x).toNat = (0#n).toNat := by
    rw [toNat_sub]
    rw [Nat.mod_eq_of_lt]
    apply Nat.mod_self
    apply toNat_lt_two_pow
  exact val_inj h1

/- ACTUAL PROOF OF BitVec.sub_self -/

example (x : BitVec n) : x - x = 0#n := by
  apply eq_of_toNat_eq
  simp only [toNat_sub]
  rw [Nat.add_comm, Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt
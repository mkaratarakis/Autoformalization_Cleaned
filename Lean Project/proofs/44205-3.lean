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
  rw [← ofInt_inj]
  -- Using the theorem for subtraction of bitvectors
  rw [ofInt_sub]
  -- Simplify the expression
  rw [Int.add_sub_cancel]
  rw [Int.cast_ofNat]
  rw [Int.ofNat_eq_coe]
  -- Show that x.toNat ≤ 2^n
  exact toNat_lt_two_pow x

/- ACTUAL PROOF OF BitVec.sub_self -/

example (x : BitVec n) : x - x = 0#n := by
  apply eq_of_toNat_eq
  simp only [toNat_sub]
  rw [Nat.add_comm, Nat.add_sub_of_le]
  · simp
  · exact Nat.le_of_lt x.isLt
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n : Nat} (x : Nat) :
  (BitVec.ofNat n x).toInt = (x : Int).bmod (2^n) := by
  apply toInt_ofNat
  exact Nat.mod_eq_bmod_int

/- ACTUAL PROOF OF BitVec.toInt_ofNat -/

example {n : Nat} (x : Nat) :
  (BitVec.ofNat n x).toInt = (x : Int).bmod (2^n) := by
  simp [toInt_eq_toNat_bmod]
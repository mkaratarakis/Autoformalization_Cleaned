import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example {i j : BitVec n} : i.toInt = j.toInt → i = j := by
  intro eq
  simp [toInt_eq_toNat_cond] at eq
  apply eq_of_toNat_eq
  revert eq
  have _ilt := i.isLt
  have _jlt := j.isLt
  split <;> split <;> omega
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example (m : Nat) (x : BitVec n) : BitVec.ofNat m x.toNat = truncate m x := by
  apply eq_of_toNat_eq
  simp
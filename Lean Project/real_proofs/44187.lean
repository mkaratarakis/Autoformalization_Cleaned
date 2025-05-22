import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp
  rw [Nat.add_comm]
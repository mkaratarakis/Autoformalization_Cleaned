import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example {n} (x y : BitVec n) :
    (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := by
  rw [toNat_sub, Nat.add_comm]
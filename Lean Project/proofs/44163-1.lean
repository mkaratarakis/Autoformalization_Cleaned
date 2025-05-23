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
  have h1 : (x - y).toNat = ((2^n - y.toNat + x.toNat) % 2^n) := by
    exact bv_sub_toNat x y
  have h2 : 2^n - y.toNat + x.toNat = x.toNat + (2^n - y.toNat) := by
    exact Nat.add_comm (2^n - y.toNat) x.toNat
  rw [h1, h2]
  rfl

/- ACTUAL PROOF OF BitVec.toNat_sub' -/

example {n} (x y : BitVec n) :
    (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := by
  rw [toNat_sub, Nat.add_comm]
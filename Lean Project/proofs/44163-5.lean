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
    simp only [BitVec.sub, BitVec.toNat, BitVec.ofNat_eq_mod, Nat.mod_add_mod]
  rw [Nat.add_comm (2^n - y.toNat) x.toNat] at h1
  exact h1

/- ACTUAL PROOF OF BitVec.toNat_sub' -/

example {n} (x y : BitVec n) :
    (x - y).toNat = ((x.toNat + (2^n - y.toNat)) % 2^n) := by
  rw [toNat_sub, Nat.add_comm]
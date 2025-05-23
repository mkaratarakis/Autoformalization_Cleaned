import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec
open BitVec


example {x y z : BitVec w} :
    x * (y + z) = x * y + x * z := by
  simp only [toNat_mul, toNat_add, toNat_mod, Nat.mul_mod, Nat.add_mod]
  rw [Nat.mul_add, Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact w
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact w
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact w
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact w
  rw [Nat.mod_eq_of_lt]
  apply Nat.mod_lt
  exact w

/- ACTUAL PROOF OF BitVec.BitVec.mul_add -/

example {x y z : BitVec w} :
    x * (y + z) = x * y + x * z := by
  apply eq_of_toNat_eq
  simp only [toNat_mul, toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [Nat.mul_mod, Nat.mod_mod (y.toNat + z.toNat),
    ← Nat.mul_mod, Nat.mul_add]
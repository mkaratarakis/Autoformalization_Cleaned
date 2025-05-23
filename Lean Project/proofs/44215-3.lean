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
  have h1 : (x * (y + z)).toNat = (x * y + x * z).toNat := by
    rw [← toNat_mul, ← toNat_add]
    simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mul, Nat.mod_add]
    rw [Nat.mul_add]
    rw [toNat_mul, toNat_add]
  exact BitVec.eq_of_toNat_eq h1

/- ACTUAL PROOF OF BitVec.BitVec.mul_add -/

example {x y z : BitVec w} :
    x * (y + z) = x * y + x * z := by
  apply eq_of_toNat_eq
  simp only [toNat_mul, toNat_add, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [Nat.mul_mod, Nat.mod_mod (y.toNat + z.toNat),
    ← Nat.mul_mod, Nat.mul_add]
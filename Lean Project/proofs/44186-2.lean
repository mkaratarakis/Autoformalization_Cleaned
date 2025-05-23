import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec
open BitVec


example {x : BitVec w} : x * 0#w = 0#w := by
  have h₁ : (x * 0#w).toNat = x.toNat * 0#w.toNat := by
    simp [toNat_mul, toNat_zero]
  rw [Nat.mul_zero] at h₁
  exact BitVec.ext h₁

/- ACTUAL PROOF OF BitVec.BitVec.mul_zero -/

example {x : BitVec w} : x * 0#w = 0#w := by
  apply eq_of_toNat_eq
  simp [toNat_mul]
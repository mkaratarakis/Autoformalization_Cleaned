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
  let n := x.toNat
  let z := 0#w.toNat
  have h₂ : (x * 0#w).toNat = n * z := by simp [BitVec.toNat_mul]
  have h₃ : n * z = 0 := by simp [Nat.mul_zero]
  rw [h₂, h₃]
  have h₄ : 0#w.toNat = 0 := by simp [BitVec.toNat_zero]
  rw [h₄]
  exact BitVec.ext (by simp)

/- ACTUAL PROOF OF BitVec.BitVec.mul_zero -/

example {x : BitVec w} : x * 0#w = 0#w := by
  apply eq_of_toNat_eq
  simp [toNat_mul]
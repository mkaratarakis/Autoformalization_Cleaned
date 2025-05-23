import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec w) : x * y = y * x := by
  have h1 : (x * y).toNat = (y * x).toNat := by
    rw [toNat_mul, toNat_mul, Nat.mul_comm]
  exact ofNat_inj w h1

/- ACTUAL PROOF OF BitVec.mul_comm -/

example (x y : BitVec w) : x * y = y * x := by
  apply eq_of_toFin_eq; simpa using Fin.mul_comm ..
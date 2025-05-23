import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec w) : x * y = y * x := by
  apply BitVec.ext
  intro i
  have h1 : ((x * y).toFin i) = ((y * x).toFin i) := by
    apply Fin.eq_of_veq
    have h2 : (x * y).toNat = (y * x).toNat := by
      have h3 : (x * y).toNat = x.toNat * y.toNat := by
        rw [BitVec.toNat_mul]
      have h4 : (y * x).toNat = y.toNat * x.toNat := by
        rw [BitVec.toNat_mul]
      rw [mul_comm, h3, h4]
    exact h2
  exact h1

/- ACTUAL PROOF OF BitVec.mul_comm -/

example (x y : BitVec w) : x * y = y * x := by
  apply eq_of_toFin_eq; simpa using Fin.mul_comm ..
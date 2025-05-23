import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec w) : x * y * z = x * (y * z) := by
  have h : (toFin x * toFin y) * toFin z = toFin x * (toFin y * toFin z) := by
    rw [Fin.mul_assoc]
  rw [← toBitVec_toFin x, ← toBitVec_toFin y, ← toBitVec_toFin z] at h
  rw [← toFin_mul]
  rw [← toFin_mul]
  rw [← toFin_mul] at h
  rw [← toBitVec_eq_toBitVec]
  exact h

/- ACTUAL PROOF OF BitVec.mul_assoc -/

example (x y z : BitVec w) : x * y * z = x * (y * z) := by
  apply eq_of_toFin_eq; simpa using Fin.mul_assoc ..
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec w) : x * y = y * x := by
  rw [← ofInt_inj, mul_comm, ofInt_inj]

/- ACTUAL PROOF OF BitVec.mul_comm -/

example (x y : BitVec w) : x * y = y * x := by
  apply eq_of_toFin_eq; simpa using Fin.mul_comm ..
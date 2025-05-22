import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example (x y z : BitVec w) : x * y * z = x * (y * z) := by
  apply eq_of_toFin_eq; simpa using Fin.mul_assoc ..
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
  apply eq_of_toNat_eq
  simp [toNat_mul]
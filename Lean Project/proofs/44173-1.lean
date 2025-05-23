import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) : 1#w * x = x := by
  rw [mul_comm]
  rw [one_mul]

/- ACTUAL PROOF OF BitVec.one_mul -/

example (x : BitVec w) : 1#w * x = x := by
  rw [BitVec.mul_comm, BitVec.mul_one]
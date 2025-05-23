import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) : x >>> 0 = x := by
  rw [lshr_zero]

/- ACTUAL PROOF OF BitVec.ushiftRight_zero_eq -/

example (x : BitVec w) : x >>> 0 = x := by
  simp [bv_toNat]
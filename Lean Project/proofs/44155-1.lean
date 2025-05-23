import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec n) : 0#n + x = x := by
  apply bv_add_zero

/- ACTUAL PROOF OF BitVec.zero_add -/

example (x : BitVec n) : 0#n + x = x := by
  simp [add_def]
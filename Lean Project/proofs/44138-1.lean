import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec n) : x + 0#n = x := by
  rw [add_zero]

/- ACTUAL PROOF OF BitVec.add_zero -/

example (x : BitVec n) : x + 0#n = x := by
  simp [add_def]
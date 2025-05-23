import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec n) : x + y = y + x := by
  have h1 := Nat.add_comm (val x) (val y)
  rw [←h1]
  rfl

/- ACTUAL PROOF OF BitVec.add_comm -/

example (x y : BitVec n) : x + y = y + x := by
  simp [add_def, Nat.add_comm]
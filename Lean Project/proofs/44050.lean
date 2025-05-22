import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (b : Bool) : (ofBool b).msb = b := by
  cases b <;> rfl

/- ACTUAL PROOF OF BitVec.msb_ofBool -/

example (b : Bool) : (ofBool b).msb = b := by
  cases b <;> simp [BitVec.msb]
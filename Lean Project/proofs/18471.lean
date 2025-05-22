import Init.Data.Fin.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Power2
import Init.Data.Int.Bitwise
import Init.Data.BitVec.Basic

open BitVec


example : ofBool true  = 1 := by
  rfl

/- ACTUAL PROOF OF BitVec.ofBool_true -/

example : ofBool true  = 1 := by
  trivial
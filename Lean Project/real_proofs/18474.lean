import Init.Data.Fin.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Power2
import Init.Data.Int.Bitwise
import Init.Data.BitVec.Basic

open BitVec



example : ofBool false = 0 := by
  trivial
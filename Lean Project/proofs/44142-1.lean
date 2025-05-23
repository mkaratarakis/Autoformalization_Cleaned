import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example : (cons a x).msb = a := by
  unfold cons
  unfold msb
  simp

/- ACTUAL PROOF OF BitVec.msb_cons -/

example : (cons a x).msb = a := by
  simp [cons, msb_cast, msb_append]
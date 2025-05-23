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
  rw [cast_concat_ofBool_concat]
  simp
  rw [msb_ofBool]
  rfl

/- ACTUAL PROOF OF BitVec.msb_cons -/

example : (cons a x).msb = a := by
  simp [cons, msb_cast, msb_append]
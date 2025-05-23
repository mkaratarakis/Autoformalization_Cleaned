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
  rw [BitVec.cast_eq]
  simp
  rw [BitVec.ofBool_eq]
  simp
  rw [BitVec.msb_eq]
  exact Bool.toFin_eq_zero a

/- ACTUAL PROOF OF BitVec.msb_cons -/

example : (cons a x).msb = a := by
  simp [cons, msb_cast, msb_append]
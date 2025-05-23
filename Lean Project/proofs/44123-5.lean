import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) :
    (~~~x).toFin = x.toFin.rev := by
  apply Fin.eq_of_val_eq
  simp only [toFin_eq_toFin_iff, val_toFin, toNat_not, Fin.val_rev, rev_toFin, Nat.sub_sub_cancel_left]

/- ACTUAL PROOF OF BitVec.toFin_not -/

example (x : BitVec w) :
    (~~~x).toFin = x.toFin.rev := by
  apply Fin.val_inj.mp
  simp only [val_toFin, toNat_not, Fin.val_rev]
  omega
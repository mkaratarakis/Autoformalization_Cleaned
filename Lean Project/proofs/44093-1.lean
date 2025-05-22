import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec v) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  have h1 : (x ||| y).toFin.1.val = (x.toFin.1.val ||| y.toFin.1.val) := by
    rw [toFin_eq_toNat, toFin_eq_toNat, toFin_eq_toNat]
    rw [Nat.bv_or_eq_nat_or]
    exact Nat.mod_eq_of_lt (Nat.bv_lt_two_pow x) (Nat.bv_lt_two_pow y)
  rw [Fin.ext_iff]
  exact h1

/- ACTUAL PROOF OF BitVec.toFin_or -/

example (x y : BitVec v) :
    BitVec.toFin (x ||| y) = BitVec.toFin x ||| BitVec.toFin y := by
  apply Fin.eq_of_val_eq
  exact (Nat.mod_eq_of_lt <| Nat.or_lt_two_pow x.isLt y.isLt).symm
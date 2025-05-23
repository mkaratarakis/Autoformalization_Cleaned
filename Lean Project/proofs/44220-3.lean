import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) : -x = ~~~x + 1 := by
  have h : (-x).toNat = (~~~x + 1).toNat := by
    rw [toNat_neg, toNat_bnot, toNat_add, toNat_one]
    simp
    rw [Nat.add_comm, Nat.sub_add_cancel]
  exact BitVec.eq_of_toNat_eq h

/- ACTUAL PROOF OF BitVec.neg_eq_not_add -/

example (x : BitVec w) : -x = ~~~x + 1 := by
  apply eq_of_toNat_eq
  simp only [toNat_neg, ofNat_eq_ofNat, toNat_add, toNat_not, toNat_ofNat, Nat.add_mod_mod]
  congr
  have hx : x.toNat < 2^w := x.isLt
  rw [Nat.sub_sub, Nat.add_comm 1 x.toNat, ← Nat.sub_sub, Nat.sub_add_cancel (by omega)]
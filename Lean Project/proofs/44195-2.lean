import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {w : Nat} : twoPow w 0 = 1#w := by
  have h1 : (twoPow w 0).toNat = 1 := by
    simp [twoPow]
    exact pow_zero 2
  have h2 : (1#w).toNat = 1 := by
    simp
  exact BitVec.eq_of_toNat_eq (h1.trans h2.symm)

/- ACTUAL PROOF OF BitVec.twoPow_zero -/

example {w : Nat} : twoPow w 0 = 1#w := by
  apply eq_of_toNat_eq
  simp
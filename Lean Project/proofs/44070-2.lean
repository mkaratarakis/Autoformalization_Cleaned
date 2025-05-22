import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (m n : Nat) : zeroExtend m 0#n = 0#m := by
  have h1 : (zeroExtend m 0#n).toNat = 0 := by
    simp [zeroExtend, toNat]
  have h2 : (0#m).toNat = 0 := by
    simp [toNat]
  exact toNat.injective h1 h2

/- ACTUAL PROOF OF BitVec.zeroExtend_zero -/

example (m n : Nat) : zeroExtend m 0#n = 0#m := by
  apply eq_of_toNat_eq
  simp [toNat_zeroExtend]
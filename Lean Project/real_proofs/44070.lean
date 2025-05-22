import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example (m n : Nat) : zeroExtend m 0#n = 0#m := by
  apply eq_of_toNat_eq
  simp [toNat_zeroExtend]
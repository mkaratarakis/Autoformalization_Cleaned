import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example {x : BitVec w} (h : w ≤ v) : x.zeroExtend' h = x.zeroExtend v := by
  apply eq_of_toNat_eq
  rw [toNat_zeroExtend, toNat_zeroExtend']
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (Nat.zero_lt_two) h)
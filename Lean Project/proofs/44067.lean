import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec n) : zeroExtend n x = x := by
  have h : (zeroExtend n x).toNat = x.toNat := by
    simp [zeroExtend, Nat.mod_eq_of_lt]
  exact (eq_of_toNat_eq h)

/- ACTUAL PROOF OF BitVec.zeroExtend_eq -/

example (x : BitVec n) : zeroExtend n x = x := by
  apply eq_of_toNat_eq
  let ⟨x, lt_n⟩ := x
  simp [truncate, zeroExtend]
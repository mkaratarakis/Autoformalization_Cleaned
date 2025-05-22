import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example : (allOnes v).toNat = 2^v - 1 := by
  rw [allOnes]
  rw [toNat_ofNat]
  rw [Nat.sub_sub_self_right]
  exact Nat.sub_zero (2^v)

/- ACTUAL PROOF OF BitVec.toNat_allOnes -/

example : (allOnes v).toNat = 2^v - 1 := by
  unfold allOnes
  simp
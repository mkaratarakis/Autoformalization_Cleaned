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
  rw [← ofNat_toNat (2^v - 1) v]
  rfl

/- ACTUAL PROOF OF BitVec.toNat_allOnes -/

example : (allOnes v).toNat = 2^v - 1 := by
  unfold allOnes
  simp
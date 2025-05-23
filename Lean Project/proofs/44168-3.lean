import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (n:Nat) : -BitVec.ofNat n 0 = BitVec.ofNat n 0 := by
  simp [BitVec.neg_eq_zero, BitVec.ofNat_eq_zero]

/- ACTUAL PROOF OF BitVec.neg_zero -/

example (n:Nat) : -BitVec.ofNat n 0 = BitVec.ofNat n 0 := by
  apply eq_of_toNat_eq ; simp
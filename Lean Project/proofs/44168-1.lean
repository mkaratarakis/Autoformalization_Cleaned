import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (n:Nat) : -BitVec.ofNat n 0 = BitVec.ofNat n 0 := by
  apply BitVec.ext
  intro i
  simp only [BitVec.neg_val, BitVec.ofNat_val, Bool.not_false_iff, BitVec.zero_val]
  have : Nat.mod (0 - 0) (2 ^ n) = 0 := by
    simp only [Nat.sub_zero, Nat.mod_self]
  rw [this]
  rfl

/- ACTUAL PROOF OF BitVec.neg_zero -/

example (n:Nat) : -BitVec.ofNat n 0 = BitVec.ofNat n 0 := by
  apply eq_of_toNat_eq ; simp
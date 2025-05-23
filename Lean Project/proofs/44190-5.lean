import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec v} : (~~~x).toNat = 2^v - 1 - x.toNat := by
  rw [Nat.sub_sub, Nat.sub_add_comm]
  rw [Nat.add_comm]
  simp only [bvnot, allOnes, bvxor_toNat]
  apply funext
  intro i
  simp only [allOnes_toNat, Nat.testBit_xor, Nat.testBit_sub_one, decide_eq_true_eq]
  split_ifs with h
  · exact (Nat.testBit_of_lt (Nat.mod_lt _ (Nat.lt_pow_self_of_lt (Fin.isLT v)))).symm
  · rw [Nat.testBit_sub_one_iff]
    exact ⟨Nat.lt_of_le_of_lt (Nat.lt_pow_self_of_lt (Fin.isLT v)) (Nat.lt_succ_self ..), rfl⟩

/- ACTUAL PROOF OF BitVec.toNat_not -/

example {x : BitVec v} : (~~~x).toNat = 2^v - 1 - x.toNat := by
  rw [Nat.sub_sub, Nat.add_comm, not_def, toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [toNat_allOnes, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  match h : BitVec.toNat x with
  | 0 => simp
  | y+1 =>
    rw [Nat.succ_eq_add_one] at h
    rw [← h]
    rw [Nat.testBit_two_pow_sub_succ (isLt _)]
    · cases w : decide (i < v)
      · simp at w
        simp [w]
        rw [Nat.testBit_lt_two_pow]
        calc BitVec.toNat x < 2 ^ v := isLt _
          _ ≤ 2 ^ i := Nat.pow_le_pow_of_le_right Nat.zero_lt_two w
      · simp
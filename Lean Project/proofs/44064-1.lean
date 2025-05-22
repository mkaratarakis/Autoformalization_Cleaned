import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n : Nat} (i : Int) :
  (BitVec.ofInt n i).toNat = (i % (2^n : Nat)).toNat := by
  have h : (BitVec.ofInt n i).toNat = (i % (2 ^ n : Nat)).toNat := by
    rw [BitVec.ofInt]
    rw [Int.toNat_eq_mod]
    rfl
  exact h

/- ACTUAL PROOF OF BitVec.toNat_ofInt -/

example {n : Nat} (i : Int) :
  (BitVec.ofInt n i).toNat = (i % (2^n : Nat)).toNat := by
  unfold BitVec.ofInt
  simp
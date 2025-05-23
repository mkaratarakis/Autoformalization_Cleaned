import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Int) : BitVec.ofInt n (x + y) =
    BitVec.ofInt n x + BitVec.ofInt n y := by
  have h₁ : BitVec.toInt (BitVec.ofInt n (x + y)) = (x + y) % (2^n) := by
    rw [BitVec.toInt_ofInt]
  have h₂ : BitVec.toInt (BitVec.ofInt n x + BitVec.ofInt n y) =
      (BitVec.toInt (BitVec.ofInt n x) + BitVec.toInt (BitVec.ofInt n y)) % (2^n) := by
    rw [BitVec.toInt_add]
    rw [BitVec.toInt_ofInt]
    rw [BitVec.toInt_ofInt]
    rw [Int.add_mod]
  rw [BitVec.ext]
  exact h₁.trans h₂.symm

/- ACTUAL PROOF OF BitVec.ofInt_add -/

example {n} (x y : Int) : BitVec.ofInt n (x + y) =
    BitVec.ofInt n x + BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp
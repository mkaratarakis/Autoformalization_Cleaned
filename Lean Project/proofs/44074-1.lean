import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) (y : Nat)
  : (x.toNat = y) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  constructor
  · intro h
    have h1 : x.toNat < 2^w := by
      apply BitVec.toNat_lt_two_pow
      exact x
    have h2 : y < 2^w := by
      rw [h] at h1
      exact h1
    have h3 : x = BitVec.ofNat w x.toNat := by
      apply BitVec.ofNat_toNat
      exact x
    rw [h] at h3
    exact ⟨h2, h3⟩
  · intro h
    have h1 := And.left h
    have h2 := And.right h
    rw [h2]
    rw [BitVec.ofNat_toNat]
    apply Nat.mod_eq_of_lt
    exact h1

/- ACTUAL PROOF OF BitVec.toNat_eq_nat -/

example (x : BitVec w) (y : Nat)
  : (x.toNat = y) ↔ (y < 2^w ∧ (x = BitVec.ofNat w y)) := by
  apply Iff.intro
  · intro eq
    simp [←eq, x.isLt]
  · intro eq
    simp [Nat.mod_eq_of_lt, eq]
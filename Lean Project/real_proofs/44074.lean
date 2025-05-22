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
  apply Iff.intro
  · intro eq
    simp [←eq, x.isLt]
  · intro eq
    simp [Nat.mod_eq_of_lt, eq]
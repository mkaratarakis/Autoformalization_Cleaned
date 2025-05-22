import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (m : Nat) (x : BitVec n) : BitVec.ofNat m x.toNat = truncate m x := by
  have h : (ofNat m x.toNat).toNat = (truncate m x).toNat := by
    simp [ofNat, truncate, toNat]
    rw [Nat.mod_mod_of_le]
    apply Nat.le_of_lt_succ
    exact m.lt_succ_self
  exact ofNat_eq_of_toNat_eq h

/- ACTUAL PROOF OF BitVec.ofNat_toNat -/

example (m : Nat) (x : BitVec n) : BitVec.ofNat m x.toNat = truncate m x := by
  apply eq_of_toNat_eq
  simp
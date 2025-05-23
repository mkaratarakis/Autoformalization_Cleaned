import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec n} {i : Nat} :
    x.sshiftRight i = BitVec.ofInt n (x.toInt >>> i) := by
  have : (x.sshiftRight i).toInt = (x.toInt >>> i) := by
    unfold sshiftRight
    rw [toInt_ofInt, Int.ashr_eq_div_of_nonneg]
    apply Int.ofNat_div
  rw [ofInt_toInt]
  exact this

/- ACTUAL PROOF OF BitVec.sshiftRight_eq -/

example {x : BitVec n} {i : Nat} :
    x.sshiftRight i = BitVec.ofInt n (x.toInt >>> i) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.sshiftRight]
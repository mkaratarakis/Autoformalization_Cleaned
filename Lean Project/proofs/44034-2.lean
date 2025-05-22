import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (n : Nat) : (0#n).toNat = 0 := by
  unfold BitVec.ofInt
  simp
  rfl

/- ACTUAL PROOF OF BitVec.toNat_zero -/

example (n : Nat) : (0#n).toNat = 0 := by
  trivial
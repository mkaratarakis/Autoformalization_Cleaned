import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} :
    (cons a x).toNat = (a.toNat <<< w) + x.toNat := by
  rw [toNat_cons]
  rw [Nat.shiftr_add (le_of_lt_succ (toNat_lt_two_pow_width x))]

/- ACTUAL PROOF OF BitVec.toNat_cons' -/

example {x : BitVec w} :
    (cons a x).toNat = (a.toNat <<< w) + x.toNat := by
  simp [cons, Nat.shiftLeft_eq, Nat.mul_comm _ (2^w), Nat.mul_add_lt_is_or, x.isLt]
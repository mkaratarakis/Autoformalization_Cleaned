import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (b : Bool) (x : BitVec w) :
    (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let hx : Nat := x.toNat
  unfold cons
  rw [toNat_append, toNat_ofBool, Nat.shiftl_eq_mul_pow]
  rw [Nat.or_def (Nat.mul _ _) hx]
  rfl

/- ACTUAL PROOF OF BitVec.toNat_cons -/

example (b : Bool) (x : BitVec w) :
    (cons b x).toNat = (b.toNat <<< w) ||| x.toNat := by
  let ⟨x, _⟩ := x
  simp [cons, toNat_append, toNat_ofBool]
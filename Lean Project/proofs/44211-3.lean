import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : Int) : BitVec.ofInt n (x * y) =
    BitVec.ofInt n x * BitVec.ofInt n y := by
  apply BitVec.ext
  intro i
  rw [ofInt_val, ofInt_val, ofInt_val, mul_val, Int.bmod_mul_bmod_self]
  rfl

/- ACTUAL PROOF OF BitVec.ofInt_mul -/

example {n} (x y : Int) : BitVec.ofInt n (x * y) =
    BitVec.ofInt n x * BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp
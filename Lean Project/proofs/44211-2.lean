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
  apply congrArg
  · apply toInt_injective
    rw [toInt_ofInt, toInt_ofInt, toInt_mul, Int.bmod_mul_bmod_self]
    rfl
  · rw [toInt_ofInt, toInt_ofInt, toInt_mul, Int.bmod_mul_bmod_self]
    rfl

/- ACTUAL PROOF OF BitVec.ofInt_mul -/

example {n} (x y : Int) : BitVec.ofInt n (x * y) =
    BitVec.ofInt n x * BitVec.ofInt n y := by
  apply eq_of_toInt_eq
  simp
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) :
    x.toInt = if x.msb then (x.toNat : Int) - (2^w : Nat) else (x.toNat : Int) := by
  by_cases h : x.msb
  · simp [h, toInt, msb, toNat]
  · simp [h, toInt, msb, toNat]

/- ACTUAL PROOF OF BitVec.toInt_eq_msb_cond -/

example (x : BitVec w) :
    x.toInt = if x.msb then (x.toNat : Int) - (2^w : Nat) else (x.toNat : Int) := by
  simp only [BitVec.toInt, ← msb_eq_false_iff_two_mul_lt]
  cases x.msb <;> rfl
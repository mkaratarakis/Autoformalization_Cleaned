import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  funext i
  by_cases h : i < k
  · simp [truncate, xor, getLsb, h]
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ (Nat.lt_succ_of_nat k))), getLsb_zero, zero_xor]
    simp [truncate, xor, getLsb, h]

/- ACTUAL PROOF OF BitVec.truncate_xor -/

example {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  ext
  simp
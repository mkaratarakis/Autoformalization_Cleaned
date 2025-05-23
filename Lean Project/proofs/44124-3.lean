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
  simp [truncate, xor, getLsb, Nat.mod_eq_of_lt]
  by_cases h : i < k
  · simp [h, getLsb_truncate]
  · exact (Nat.not_lt_of_ge h).elim

/- ACTUAL PROOF OF BitVec.truncate_xor -/

example {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  ext
  simp
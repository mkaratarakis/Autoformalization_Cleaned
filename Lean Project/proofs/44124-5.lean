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
    exact (getLsb_xor _ _ _).symm
  · simp [truncate, xor, getLsb, h]
    exact zero_xor _

/- ACTUAL PROOF OF BitVec.truncate_xor -/

example {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  ext
  simp
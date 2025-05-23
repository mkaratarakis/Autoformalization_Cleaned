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
  split_ifs with h
  . simp [h]
  . simp [h]

/- ACTUAL PROOF OF BitVec.truncate_xor -/

example {x y : BitVec w} :
    (x ^^^ y).truncate k = x.truncate k ^^^ y.truncate k := by
  ext
  simp
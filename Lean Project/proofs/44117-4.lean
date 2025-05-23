import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x y : BitVec w} :
    (x ||| y).truncate k = x.truncate k ||| y.truncate k := by
  funext i
  have h1 : (x ||| y).getLsb i = (x.getLsb i || y.getLsb i) := by
    rw [BitVec.getLsb_or]
  have h2 : (x.truncate k).getLsb i = x.getLsb i := by
    simp [truncate, BitVec.ofInt_getLsb]
  have h3 : (y.truncate k).getLsb i = y.getLsb i := by
    simp [truncate, BitVec.ofInt_getLsb]
  rw [truncate, BitVec.ofInt_getLsb, BitVec.getLsb_or, h2, h3]
  exact h1

/- ACTUAL PROOF OF BitVec.truncate_or -/

example {x y : BitVec w} :
    (x ||| y).truncate k = x.truncate k ||| y.truncate k := by
  ext
  simp
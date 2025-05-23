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
  funext i hi
  have h₁ : (x ||| y).truncate k = (x ||| y).extract 0 k := by rw [BitVec.truncate_eq_extract]
  have h₂ : (x.truncate k ||| y.truncate k) = (x.extract 0 k ||| y.extract 0 k) := by rw [BitVec.truncate_eq_extract, BitVec.truncate_eq_extract]
  rw [h₁, h₂, BitVec.extract_or]
  rfl

/- ACTUAL PROOF OF BitVec.truncate_or -/

example {x y : BitVec w} :
    (x ||| y).truncate k = x.truncate k ||| y.truncate k := by
  ext
  simp
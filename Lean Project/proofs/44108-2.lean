import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x y : BitVec w} :
    (x &&& y).truncate k = x.truncate k &&& y.truncate k := by
  funext i
  have h₁ : (x &&& y).truncate k = (x &&& y).extract 0 k := by
    simp [truncate]
  have h₂ : (x.truncate k &&& y.truncate k) = (x.extract 0 k &&& y.extract 0 k) := by
    simp [truncate]
    simp [and]
  rw [h₁, h₂]
  have h₃ : (x &&& y).extract 0 k = (x.extract 0 k &&& y.extract 0 k) := by
    simp [extract]
    simp [and]
  rw [h₃]
  rfl

/- ACTUAL PROOF OF BitVec.truncate_and -/

example {x y : BitVec w} :
    (x &&& y).truncate k = x.truncate k &&& y.truncate k := by
  ext
  simp
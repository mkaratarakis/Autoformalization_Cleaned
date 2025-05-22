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
  have h₁ : (x &&& y).truncate k i = (x &&& y) i := by
    apply truncate_eq_self
  have h₂ : (x.truncate k &&& y.truncate k) i = (x i &&& y i) := by
    apply and_truncate_eq
  rw [h₁, h₂]
  rfl

/- ACTUAL PROOF OF BitVec.truncate_and -/

example {x y : BitVec w} :
    (x &&& y).truncate k = x.truncate k &&& y.truncate k := by
  ext
  simp
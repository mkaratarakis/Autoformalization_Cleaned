import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} {r : Nat} :
    x.rotateLeft (r % w) = x.rotateLeft r := by
  have h1 : r % w % w = r % w := by simp
  rw [h1]
  exact rfl

/- ACTUAL PROOF OF BitVec.rotateLeft_mod_eq_rotateLeft -/

example {x : BitVec w} {r : Nat} :
    x.rotateLeft (r % w) = x.rotateLeft r := by
  simp only [rotateLeft, Nat.mod_mod]
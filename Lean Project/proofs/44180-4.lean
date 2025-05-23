import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} {r : Nat} :
    x.rotateRight (r % w) = x.rotateRight r := by
  rw [rotateRight_def, rotateRight_def]
  have h1 : (r % w) % w = r % w := by
    exact Nat.mod_mod _ _
  have h2 : w - (r % w) = w - r % w := by
    rw [Nat.sub_mod]
  rw [h1, h2]

/- ACTUAL PROOF OF BitVec.rotateRight_mod_eq_rotateRight -/

example {x : BitVec w} {r : Nat} :
    x.rotateRight (r % w) = x.rotateRight r := by
  simp only [rotateRight, Nat.mod_mod]
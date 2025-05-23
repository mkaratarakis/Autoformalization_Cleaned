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
  rw [← Nat.mod_mod_of_pos]
  exact Nat.mod_eq_of_lt (Nat.mod_lt r (by norm_num))

/- ACTUAL PROOF OF BitVec.rotateLeft_mod_eq_rotateLeft -/

example {x : BitVec w} {r : Nat} :
    x.rotateLeft (r % w) = x.rotateLeft r := by
  simp only [rotateLeft, Nat.mod_mod]
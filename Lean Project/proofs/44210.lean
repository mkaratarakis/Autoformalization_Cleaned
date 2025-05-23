import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateLeft r = x.rotateLeftAux r := by
  rw [rotateLeft, rotateLeftAux]
  simp [Nat.mod_eq_of_lt hr]
  rfl

/- ACTUAL PROOF OF BitVec.rotateLeft_eq_rotateLeftAux_of_lt -/

example {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateLeft r = x.rotateLeftAux r := by
  simp only [rotateLeft, Nat.mod_eq_of_lt hr]
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateRight r = x.rotateRightAux r := by
  rw [rotateRight]
  rw [Nat.mod_eq_of_lt hr]

/- ACTUAL PROOF OF BitVec.rotateRight_eq_rotateRightAux_of_lt -/

example {x : BitVec w} {r : Nat} (hr : r < w) :
    x.rotateRight r = x.rotateRightAux r := by
  simp only [rotateRight, Nat.mod_eq_of_lt hr]
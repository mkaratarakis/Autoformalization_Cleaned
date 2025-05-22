import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec w) :
    x &&& y = y &&& x := by
  funext i
  have h : (x &&& y).getLsb(i) = (y &&& x).getLsb(i) := by
    simp only [BitVec.getLsb_and, Bool.and_comm]
  exact h

/- ACTUAL PROOF OF BitVec.and_comm -/

example (x y : BitVec w) :
    x &&& y = y &&& x := by
  ext i
  simp [Bool.and_comm]
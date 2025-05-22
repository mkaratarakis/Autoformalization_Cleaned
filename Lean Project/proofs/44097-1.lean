import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec w) :
    x ^^^ y ^^^ z = x ^^^ (y ^^^ z) := by
  funext i
  simp only [getElem, bvxor, bvxor_def]
  exact bool.xor_assoc

/- ACTUAL PROOF OF BitVec.xor_assoc -/

example (x y z : BitVec w) :
    x ^^^ y ^^^ z = x ^^^ (y ^^^ z) := by
  ext i
  simp [Bool.xor_assoc]
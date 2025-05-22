import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  funext i
  calc
    (x ||| y ||| z).getLsb i
      = ((x ||| y).getLsb i : Bool) || (z.getLsb i : Bool) := rfl
    ... = (x.getLsb i || y.getLsb i) || z.getLsb i := rfl
    ... = x.getLsb i || (y.getLsb i || z.getLsb i) := or_assoc (x.getLsb i) (y.getLsb i) (z.getLsb i)
    ... = x.getLsb i || ((y ||| z).getLsb i : Bool) := rfl
    ... = (x ||| (y ||| z)).getLsb i := rfl

/- ACTUAL PROOF OF BitVec.or_assoc -/

example (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  ext i
  simp [Bool.or_assoc]
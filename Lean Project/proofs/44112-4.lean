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
  ext i
  calc
    (x ||| y ||| z)[i]
      = (x ||| y)[i] || (z[i]) := rfl
    ... = (x[i] || y[i]) || z[i] := rfl
    ... = x[i] || (y[i] || z[i]) := or_assoc (x[i]) (y[i]) (z[i])
    ... = x[i] || ((y ||| z)[i]) := rfl
    ... = (x ||| (y ||| z))[i] := rfl

/- ACTUAL PROOF OF BitVec.or_assoc -/

example (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  ext i
  simp [Bool.or_assoc]
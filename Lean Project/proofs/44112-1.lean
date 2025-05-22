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
    (x ||| y ||| z).getLsb i = (x.getLsb i) || (y.getLsb i) || (z.getLsb i) := rfl
    _ = (x.getLsb i) || ((y.getLsb i) || (z.getLsb i)) := by rw [Bool.bor_assoc]
    _ = (x ||| (y ||| z)).getLsb i := rfl

/- ACTUAL PROOF OF BitVec.or_assoc -/

example (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  ext i
  simp [Bool.or_assoc]
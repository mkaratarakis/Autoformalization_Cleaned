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
  have h1 : ((x ||| y) ||| z).getLsb i = (x.getLsb i || y.getLsb i) || z.getLsb i := by simp [getLsb_bor]
  have h2 : (x ||| (y ||| z)).getLsb i = x.getLsb i || (y.getLsb i || z.getLsb i) := by simp [getLsb_bor]
  rw [h1, h2]
  exact or_assoc (x.getLsb i) (y.getLsb i) (z.getLsb i)

/- ACTUAL PROOF OF BitVec.or_assoc -/

example (x y z : BitVec w) :
    x ||| y ||| z = x ||| (y ||| z) := by
  ext i
  simp [Bool.or_assoc]
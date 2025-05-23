import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w} :
    x.replicate (n + 1) =
    (x ++ replicate n x).cast (by rw [Nat.mul_succ]; omega) := by
  rw [replicate_succ]
  rfl

/- ACTUAL PROOF OF BitVec.replicate_succ_eq -/

example {x : BitVec w} :
    x.replicate (n + 1) =
    (x ++ replicate n x).cast (by rw [Nat.mul_succ]; omega) := by
  simp [replicate]
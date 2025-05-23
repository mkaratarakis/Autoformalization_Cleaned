import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {w : Nat} (x : BitVec w) (n m : Nat) :
    (x <<< n) <<< m = x <<< (n + m) := by
  simp [shiftr_eq_shiftr_add]
  rfl

/- ACTUAL PROOF OF BitVec.shiftLeft_shiftLeft -/

example {w : Nat} (x : BitVec w) (n m : Nat) :
    (x <<< n) <<< m = x <<< (n + m) := by
  rw [shiftLeft_add]
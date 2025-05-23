import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {x : BitVec w₁} {y : BitVec w₂} {z : BitVec w₃} :
    x <<< y <<< z = x <<< (y.toNat + z.toNat) := by
  rw [← shll_add_eq_shll_shll]
  exact ((x <<< y) <<< z)
example (x : BitVec w) (n m : ℕ) : x <<< (n + m) = (x <<< n) <<< m := by
  induction m with
  | zero =>
    simp [shll, Nat.add_zero]
  | succ m ih =>
    simp [shll, Nat.add_succ]
    rw [ih]
    rw [← shll_succ]
    simp [Nat.succ_add]

/- ACTUAL PROOF OF BitVec.shiftLeft_shiftLeft' -/

example {x : BitVec w₁} {y : BitVec w₂} {z : BitVec w₃} :
    x <<< y <<< z = x <<< (y.toNat + z.toNat) := by
  simp [shiftLeft_add]
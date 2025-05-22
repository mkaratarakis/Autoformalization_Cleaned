import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example {x y z : BitVec w} : x = z - y ↔ x + y = z := by
  apply Iff.intro <;> intro h
  · simp [h, sub_add_cancel]
  · simp [←h, add_sub_cancel]
import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec



example (x y : BitVec w) : x - y + y = x := by
  rw [sub_toAdd, BitVec.add_assoc, BitVec.add_comm _ y,
      ← BitVec.add_assoc, ← sub_toAdd, add_sub_cancel]
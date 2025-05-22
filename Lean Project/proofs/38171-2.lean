import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String
open Pos


example (c : Char) : ((0 : Pos) + c).byteIdx = c.utf8Size := by
  rw [add_zero]
  exact UTF8.size c

/- ACTUAL PROOF OF String.Pos.zero_addChar_byteIdx -/

example (c : Char) : ((0 : Pos) + c).byteIdx = c.utf8Size := by
  simp only [addChar_byteIdx, byteIdx_zero, Nat.zero_add]
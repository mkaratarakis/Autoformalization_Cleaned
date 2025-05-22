import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String
open Pos


example (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← byteIdx_add_zero s]
  rfl

/- ACTUAL PROOF OF String.Pos.zero_addString_eq -/

example (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← zero_addString_byteIdx]
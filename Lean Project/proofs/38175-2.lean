import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String
open Pos


example (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  have h : (0 + s).byteIdx = s.utf8ByteSize := by
    rfl
  rw [← h]
  rfl

/- ACTUAL PROOF OF String.Pos.zero_addString_eq -/

example (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ := by
  rw [← zero_addString_byteIdx]
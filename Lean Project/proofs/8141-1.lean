import Init.Data.ByteArray
import Init.Data.String.Extra

open String
open Iterator


example (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  let s := i.toString
  let pos := i.pos
  have h1 : pos.byteIdx < s.endPos.byteIdx := h
  have h2 : pos.byteIdx < (s.next pos).byteIdx :=
    String.lt_next s pos
  calc
    sizeOf i.next = s.utf8ByteSize - (s.next pos).byteIdx := rfl
    _ < s.utf8ByteSize - pos.byteIdx := Nat.sub_lt_sub_left (String.lt_next s pos) _
    _ = sizeOf i := rfl

/- ACTUAL PROOF OF String.Iterator.sizeOf_next_lt_of_hasNext -/

example (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  exact Nat.sub_lt_sub_left h (String.lt_next s pos)
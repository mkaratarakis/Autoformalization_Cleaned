import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open Substring


example (s : Substring) (i : String.Pos) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  unfold next
  split
  · intro h'
    apply h
    rw [←String.Pos.add_byteIdx, h']
    exact String.Pos.byteIdx_add_cancel
  · simp
    apply lt_tsub_iff_right.2
    simp
    rw [String.Pos.add_byteIdx]
    apply String.Pos.byteIdx_lt_next_byteIdx
    rw [←String.Pos.add_byteIdx] at h
    exact h

/- ACTUAL PROOF OF Substring.lt_next -/

example (s : Substring) (i : String.Pos) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  simp [next]; rw [if_neg ?a]
  case a =>
    refine mt (congrArg String.Pos.byteIdx) (Nat.ne_of_lt ?_)
    exact (Nat.add_comm .. ▸ Nat.add_lt_of_lt_sub h :)
  apply Nat.lt_sub_of_add_lt
  rw [Nat.add_comm]; apply String.lt_next
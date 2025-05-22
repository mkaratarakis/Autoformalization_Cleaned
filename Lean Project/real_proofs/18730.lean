import Init.Data.Array.Basic
import Init.Data.Array.Subarray

open Subarray



example {s : Subarray α} : s.size ≤ s.array.size := by
  let {array, start, stop, start_le_stop, stop_le_array_size} := s
  simp [size]
  apply Nat.le_trans (Nat.sub_le stop start)
  assumption
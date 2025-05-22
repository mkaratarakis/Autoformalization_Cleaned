import Init.Data.Array.Basic
import Init.Data.Array.Subarray

open Subarray


example {s : Subarray α} : s.size ≤ s.array.size := by
  let ⟨array, start, stop, h₁, h₂⟩ := s
  simp only [size]
  exact Nat.sub_le stop start h₂

/- ACTUAL PROOF OF Subarray.size_le_array_size -/

example {s : Subarray α} : s.size ≤ s.array.size := by
  let {array, start, stop, start_le_stop, stop_le_array_size} := s
  simp [size]
  apply Nat.le_trans (Nat.sub_le stop start)
  assumption
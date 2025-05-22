import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (l : List α) : zipIdx l.unzip = (range l.length, l) := by
  rw [zipIdx.eq_def]
  rw [unzip_zip]
  rfl

/- ACTUAL PROOF OF List.unzip_enum_eq_prod -/

example (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]
import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} (h):
    (List.zipWith f as bs).head h = f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all)) := by
  rw [head_eq_head?]
  rw [head?_eq_some_of_mem]
  · exact h
  rw [head?_eq_some_of_mem]
  · exact h
  simp only [head?, zipWith]
  rw [head?_eq_some_of_mem]
  · exact h
  rw [head?_eq_some_of_mem]
  · exact h
  simp only [head?, zipWith]
  exact h

/- ACTUAL PROOF OF List.head_zipWith -/

example {f : α → β → γ} (h):
    (List.zipWith f as bs).head h = f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all)) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWith, head?_eq_head, head?_eq_head]
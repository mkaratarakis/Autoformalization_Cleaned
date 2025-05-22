import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} (h):
    (List.zipWith f as bs).head h = f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all)) := by
  have h1 : zipWith f as bs ≠ [] := h
  simp only [zipWith, head, head?, Option.some.injEq] at h1
  exact h1

/- ACTUAL PROOF OF List.head_zipWith -/

example {f : α → β → γ} (h):
    (List.zipWith f as bs).head h = f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all)) := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWith, head?_eq_head, head?_eq_head]
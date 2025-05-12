import Mathlib.Logic.Function.Conjugate
import Mathlib.Logic.Function.Iterate

open Function
variable {α : Type u} {β : Type v}
open Function (Commute)
variable (f : α → α)

example (m n : ℕ) (x : α) : f^[m + n] x = f^[m] (f^[n] x) := by
  rw [iterate_add f m n]
  refl

/- ACTUAL PROOF OF Function.iterate_add_apply -/

example (m n : ℕ) (x : α) : f^[m + n] x = f^[m] (f^[n] x) := by
  rw [iterate_add f m n]
  rfl
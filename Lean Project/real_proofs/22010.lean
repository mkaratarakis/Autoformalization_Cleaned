import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List



example {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]
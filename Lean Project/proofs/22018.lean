import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l with
  | nil =>
    simp
  | cons a l' ih =>
    simp [ih]

/- ACTUAL PROOF OF List.length_pmap -/

example {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l
  · rfl
  · simp only [*, pmap, length]
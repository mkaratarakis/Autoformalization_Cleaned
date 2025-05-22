import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List



example {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l
  · rfl
  · simp only [*, pmap, map]
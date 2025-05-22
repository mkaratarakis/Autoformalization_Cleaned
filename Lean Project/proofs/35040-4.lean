import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ := by
  constructor
  · rintro ⟨s, t, h⟩
    rw [← h, reverse_append, reverse_append, reverse_reverse]
    exact Sublist.append_right (Sublist.append_left (Sublist.refl _) _) _
  · rintro ⟨s, t, h⟩
    rw [← h, reverse_append, reverse_append, reverse_reverse]
    exact Sublist.append_right (Sublist.append_left (Sublist.refl _) _) _

/- ACTUAL PROOF OF List.reverse_infix -/

example : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ := by
  refine ⟨fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩, fun ⟨s, t, e⟩ => ⟨reverse t, reverse s, ?_⟩⟩
  · rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
      reverse_reverse]
  · rw [append_assoc, ← reverse_append, ← reverse_append, e]
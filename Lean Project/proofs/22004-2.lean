import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  rw [pmap.eq_def, List.mem_map]
  constructor
  · rintro ⟨_, _, h⟩
    exact ⟨_, h.left, h.right⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨_, _, ⟨h, rfl⟩⟩

/- ACTUAL PROOF OF List.mem_pmap -/

example {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]
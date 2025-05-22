import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp [pmap]
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp
    constructor
    · rintro (rfl | hin)
      · exact ⟨hd, Mem.head _, rfl⟩
      · obtain ⟨a, h, rfl⟩ := ih hin
        exact ⟨a, Mem.tail _ h, rfl⟩
    · rintro ⟨a, (Mem.head _ | Mem.tail _ h), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (ih ⟨a, h, rfl⟩)

/- ACTUAL PROOF OF List.mem_pmap -/

example {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _) (h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, Subtype.exists, eq_comm]
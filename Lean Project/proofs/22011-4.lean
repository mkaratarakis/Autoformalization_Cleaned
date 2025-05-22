import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  unfold pmap
  simp [attach, attachWith, map_pmap]
  exact pmap_congr_left f l H fun a h => rfl

/- ACTUAL PROOF OF List.pmap_eq_map_attach -/

example {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, attachWith, map_pmap]; exact pmap_congr l fun _ _ _ _ => rfl
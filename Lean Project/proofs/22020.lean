import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l with
  | nil =>
    rfl
  | cons a l' ih =>
    simp only [pmap, map, ih]

/- ACTUAL PROOF OF List.pmap_eq_map -/

example (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l
  · rfl
  · simp only [*, pmap, map]
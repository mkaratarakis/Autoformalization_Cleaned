import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil_iff.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  cases l with
  | nil =>
    exfalso
    exact hl₂ rfl
  | cons hd tl =>
    have : tl ≠ [] := by
      intro h
      apply hl₂
      rw [h]
    simp only [pmap, getLast]
    rw [getLast_cons_ne_nil _ this]
    exact congrArg (fun l => f (l.getLast this) (hl₁ _ (List.getLast_mem this))) (getLast_eq_of_cons_ne_nil _ this)

/- ACTUAL PROOF OF List.getLast_pmap -/

example (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  induction l with
  | nil => apply (hl₂ rfl).elim
  | cons l_hd l_tl l_ih =>
    by_cases hl_tl : l_tl = []
    · simp [hl_tl]
    · simp only [pmap]
      rw [getLast_cons, l_ih _ hl_tl]
      simp only [getLast_cons hl_tl]
import Init.Data.List.Count
import Init.Data.Subtype
import Init.Data.List.Attach

open List


example (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).getLast (mt List.pmap_eq_nil.1 hl₂) =
      f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂)) := by
  have : l ≠ [] := hl₂
  cases l with
  | [] =>
    exfalso
    apply this
  | x :: xs =>
    cases xs with
    | [] =>
      simp only [pmap, getLast]
      rfl
    | y :: ys =>
      simp only [pmap, getLast]
      rw [getLast_cons_ne_nil xs hl₂]
      exact congrArg (fun l => f (l.getLast hl₂) (hl₁ _ (List.getLast_mem hl₂))) (xs.getLast_eq_of_cons_ne_nil hl₂)

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
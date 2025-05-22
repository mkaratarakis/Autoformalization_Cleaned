import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}

example (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  induction l with
  | nil =>
    -- Base case: l is nil
    simp [countP]
  | a :: l ih =>
    -- Inductive step: l is a :: l
    simp [countP]
    by_cases h1 : p a
    · -- Case 1: p a = true
      simp [h1]
      have h2 : q a := h _ (by simp) h1
      simp [h2]
      exact Nat.le_add_right (ih (by simp)) 1
    · -- Case 2: p a = false
      simp [h1]
      exact Nat.le_add_right (ih (by simp)) (if q a then 1 else 0)

/- ACTUAL PROOF OF List.countP_mono_left -/

example (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  induction l with
  | nil => apply Nat.le_refl
  | cons a l ihl =>
    rw [forall_mem_cons] at h
    have ⟨ha, hl⟩ := h
    simp [countP_cons]
    cases h : p a
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      apply Nat.le_trans ?_ (Nat.le_add_right _ _)
      apply ihl hl
    · simp only [↓reduceIte, ha h, succ_le_succ_iff]
      apply ihl hl
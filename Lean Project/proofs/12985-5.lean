import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}

example (h : ∀ x ∈ l, p x → q x) : countP p l ≤ countP q l := by
  induction l with
  | nil =>
    simp [countP]
  | cons a l ih =>
    simp [countP]
    by_cases h1 : p a
    · -- Case 1: p a = true
      have h2 : q a := h a (by simp) h1
      simp [h1, h2]
      apply Nat.le_add_right
      apply ih
      intro b hb
      apply h
      simp
      exact hb
    · -- Case 2: p a = false
      simp [h1]
      apply Nat.le_add_right
      apply ih
      intro b hb
      apply h
      simp
      exact hb

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
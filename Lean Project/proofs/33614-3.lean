import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example {l : List α} (h : ∀ a ∈ l, ¬ p a ∨ ¬ q a) :
    (l.eraseP p).eraseP q = (l.eraseP q).eraseP p := by
  induction l with
  | nil =>
    simp
  | cons a l ih =>
    have h_head : ¬ p a ∨ ¬ q a := h a (by simp)
    rcases h_head with (hp | hq)
    · -- Case where ¬ p a
      simp [hp]
      rw [ih fun b hb => h b (mem_cons_of_mem _ _ hb)]
    · -- Case where ¬ q a
      simp [hq]
      rw [ih fun b hb => h b (mem_cons_of_mem _ _ hb)]

/- ACTUAL PROOF OF List.eraseP_comm -/

example {l : List α} (h : ∀ a ∈ l, ¬ p a ∨ ¬ q a) :
    (l.eraseP p).eraseP q = (l.eraseP q).eraseP p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [eraseP_cons]
    by_cases h₁ : p a
    · by_cases h₂ : q a
      · simp_all
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]
    · by_cases h₂ : q a
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]
      · simp [h₁, h₂, ih (fun b m => h b (mem_cons_of_mem _ m))]
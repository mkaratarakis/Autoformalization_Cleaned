import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat


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
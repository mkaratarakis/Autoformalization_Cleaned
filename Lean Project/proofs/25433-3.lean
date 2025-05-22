import Init.Data.List.TakeDrop
import Init.Data.List.Monadic

open List
open Nat

example [Monad m] [LawfulMonad m] (l₁ l₂ : List α) (f : α → m PUnit) :
    (l₁ ++ l₂).forM f = (do l₁.forM f; l₂.forM f) := by
  induction l₁ with
  | nil =>
    simp [forM, nil_append]
  | cons head tail ih =>
    simp [forM, cons_append]
    rw [ih]
    congr
    exact bind_assoc (f head) (fun _ => tail.forM f) (l₂.forM f)

/- ACTUAL PROOF OF List.forM_append -/

example [Monad m] [LawfulMonad m] (l₁ l₂ : List α) (f : α → m PUnit) :
    (l₁ ++ l₂).forM f = (do l₁.forM f; l₂.forM f) := by
  induction l₁ <;> simp [*]
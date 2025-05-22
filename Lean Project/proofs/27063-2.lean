import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {δ : Type _} (f : α → β) (g : Option γ → Option δ → α) (l : List γ) (l' : List δ) :
    map f (zipWithAll g l l') = zipWithAll (fun x y => f (g x y)) l l' := by
  induction l with
  | nil =>
    simp [zipWithAll, map]
  | cons hd tl ih =>
    cases l' with
    | nil =>
      simp [zipWithAll, map]
    | cons head tail =>
      simp [zipWithAll, map]
      rw [ih (head :: tail)]
      simp

/- ACTUAL PROOF OF List.map_zipWithAll -/

example {δ : Type _} (f : α → β) (g : Option γ → Option δ → α) (l : List γ) (l' : List δ) :
    map f (zipWithAll g l l') = zipWithAll (fun x y => f (g x y)) l l' := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    cases l' <;> simp_all
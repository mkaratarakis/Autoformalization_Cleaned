import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction l with
  | nil =>
    simp [zipWith, map]
  | cons hd tl ih =>
    cases l' with
    | nil =>
      simp [zipWith, map]
    | cons head tail =>
      simp [zipWith, map, ih]

/- ACTUAL PROOF OF List.map_zipWith -/

example {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' := by
  induction l generalizing l' with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · simp [hl]
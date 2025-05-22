import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).dropWhile p = (l.dropWhile (p ∘ f)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [map_cons, dropWhile_cons]
    split <;> simp_all
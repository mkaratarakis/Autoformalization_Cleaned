import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (p : α → Bool) (l : List α) (w) :
    (l.takeWhile p).head w = l.head (by rintro rfl; simp_all) := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head_cons]
    simp only [takeWhile_cons] at w
    split <;> simp_all
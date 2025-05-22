import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (p : α → Bool) (l : List α) : (l.takeWhile p).head? = l.head?.filter p := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [takeWhile_cons, head?_cons, Option.filter_some]
    split <;> simp
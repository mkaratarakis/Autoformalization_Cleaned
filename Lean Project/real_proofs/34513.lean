import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} :
    (l.dropWhile p).any (fun x => !p x) = !l.all p := by
  induction l with
  | nil => rfl
  | cons h t ih => by_cases p h <;> simp_all
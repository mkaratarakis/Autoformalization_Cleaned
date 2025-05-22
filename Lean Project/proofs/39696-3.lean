import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil =>
    exfalso
    apply Option.noConfusion w
  | cons h l ih =>
    by_cases h1 : f h = some b
    · exists h
      constructor
      · left
        exact h
      · exact h1
    · by_cases h2 : l.findSome? f = some b
      · cases ih h2 with
        | intro a ha =>
          exists a
          constructor
          · right
            exact ha.left
          · exact ha.right
      · simp [findSome?, h1, h2] at w

/- ACTUAL PROOF OF List.exists_of_findSome?_eq_some -/

example {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all
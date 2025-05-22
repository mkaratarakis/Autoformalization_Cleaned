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
    case some b =>
  | cons h l ih =>
    by_cases h1 : f h = some b
    · exists h
      constructor
      · left
        exact h
      · exact h1
    · by_cases h2 : findSome? f l = some b
      · have : l.findSome? f = some b := h2
        cases ih this with
        | intro a _ =>
          exists a
          constructor
          · right
            exact a
          · exact h2
      · have : findSome? f l = none := (Option.ne_iff_eq_none.mpr h2)
        simp [findSome?, this] at w

/- ACTUAL PROOF OF List.exists_of_findSome?_eq_some -/

example {l : List α} {f : α → Option β} (w : l.findSome? f = some b) :
    ∃ a, a ∈ l ∧ f a = b := by
  induction l with
  | nil => simp_all
  | cons h l ih =>
    simp_all only [findSome?_cons, mem_cons, exists_eq_or_imp]
    split at w <;> simp_all
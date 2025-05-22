import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  rw [filterMap_eq_filter, filterMap_eq_filter, takeWhile_filterMap]
  simp

def filterMap (f : α → Option β) : List α → List β
  | [] => []
  | a :: l =>
    match f a with
    | none => filterMap l
    | some b => b :: filterMap l
example (p : α → Bool) (l : List α) :
    filterMap (fun a => if p a then some a else none) l = filter p l := by
  induction l <;> simp [filterMap, filter, *]

theorem takeWhile_filterMap (p : α → Bool) (f : α → Option β) (l : List α) :
    takeWhile p (filterMap f l) = filterMap f (takeWhile (fun a => (f a).isSome → p (Option.get (f a))) l) := by
  induction l <;> simp [takeWhile, filterMap, *]

/- ACTUAL PROOF OF List.takeWhile_filter -/

example (p q : α → Bool) (l : List α) :
    (l.filter p).takeWhile q = (l.takeWhile fun a => !p a || q a).filter p := by
  simp [← filterMap_eq_filter, takeWhile_filterMap]
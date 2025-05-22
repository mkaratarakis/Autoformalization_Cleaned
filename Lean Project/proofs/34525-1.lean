import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).dropWhile p = (l.dropWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    by_cases h : (f x).isSome
    · rcases h with ⟨b, rfl⟩
      by_cases hp : p b
      · simp [hp]
        rw [ih]
      · simp [hp]
        rw [dropWhile_eq_nil.2 (fun y hy => by rw [mem_filterMap] at hy; exact hp)]
    · simp [h]
      rw [dropWhile_eq_nil.2 (fun y hy => by rw [mem_filterMap] at hy; exact (Option.all_eq_true.2 hy).2)]
      rw [ih]

/- ACTUAL PROOF OF List.dropWhile_filterMap -/

example (f : α → Option β) (p : β → Bool) (l : List α) :
    (l.filterMap f).dropWhile p = (l.dropWhile fun a => (f a).all p).filterMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap_cons]
    split <;> rename_i h
    · simp only [dropWhile_cons, h]
      split <;> simp_all
    · simp [dropWhile_cons, h, ih]
      split <;> simp_all [filterMap_cons]
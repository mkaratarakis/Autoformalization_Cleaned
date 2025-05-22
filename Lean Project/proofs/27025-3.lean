import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example (f : α → β → γ) (l la : List α) (l' lb : List β)
    (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  induction l generalizing l'
  · simp [zipWith, h]
    rw [length_eq_zero_iff] at h
    rw [h]
    simp
  · cases l'
    · contradiction
    · simp [zipWith, *, append_assoc]
      exact (ih_1 _ rfl).symm

/- ACTUAL PROOF OF List.zipWith_append -/

example (f : α → β → γ) (l la : List α) (l' lb : List β)
    (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb := by
  induction l generalizing l' with
  | nil =>
    have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp [this]
  | cons hl tl ih =>
    cases l' with
    | nil => simp at h
    | cons head tail =>
      simp only [length_cons, Nat.succ.injEq] at h
      simp [ih _ h]
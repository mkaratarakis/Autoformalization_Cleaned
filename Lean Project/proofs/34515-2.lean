import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example : l.Pairwise R ↔ (∀ {a b}, [a,b] <+ l → R a b) := by
  constructor
  · intro h a b hab
    induction l generalizing a b
    | nil =>
      exfalso
      exact not_mem_nil a hab.subset
    | cons hd tl IH =>
      rw [List.pairwise_cons] at h
      cases h
      ·
        cases hab
        case sublist.cons2 _ _ hab =>
          apply IH h_right
          exact hab.subset
        case sublist.cons _ _ hab =>
          apply h_left
          exact hab.subset
      ·
        apply IH h_right hab
  · intro h
    induction l
    | nil => simp
    | cons hd tl IH =>
      rw [List.pairwise_cons]
      constructor
      · intro x hx
        apply h
        rw [List.cons_sublist_cons, List.singleton_sublist]
        exact hx
      · apply IH.mpr
        intro a b hab
        apply h
        exact hab.cons _

/- ACTUAL PROOF OF List.pairwise_iff_forall_sublist -/

example : l.Pairwise R ↔ (∀ {a b}, [a,b] <+ l → R a b) := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    rw [List.pairwise_cons]
    constructor <;> intro h
    · intro
      | a, b, .cons _ hab => exact IH.mp h.2 hab
      | _, b, .cons₂ _ hab => refine h.1 _ (hab.subset ?_); simp
    · constructor
      · intro x hx
        apply h
        rw [List.cons_sublist_cons, List.singleton_sublist]
        exact hx
      · apply IH.mpr
        intro a b hab
        apply h; exact hab.cons _
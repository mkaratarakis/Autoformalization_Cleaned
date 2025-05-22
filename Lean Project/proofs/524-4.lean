import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat

example {l : List α} (pa : ¬p a) : a ∈ l.eraseP p ↔ a ∈ l := by
  apply Iff.intro
  · intro h
    induction l generalizing a
    · contradiction
    · case cons x xs IH =>
      simp [eraseP]
      by_cases hp : p x
      · simp [hp] at h
        cases h
        · left
          exact h
        · right
          exact IH h
      · simp [hp] at *
        cases h
        · left
          exact h
        · right
          exact IH h
  · intro h
    induction l generalizing a
    · contradiction
    · case cons x xs IH =>
      simp [eraseP]
      by_cases hp : p x
      · simp [hp]
        left
        apply Eq.substr h
      · simp [hp] at *
        cases h
        · left
          exact h
        · right
          exact IH h

/- ACTUAL PROOF OF List.mem_eraseP_of_neg -/

example {l : List α} (pa : ¬p a) : a ∈ l.eraseP p ↔ a ∈ l := by
  refine ⟨mem_of_mem_eraseP, fun al => ?_⟩
  match exists_or_eq_self_of_eraseP p l with
  | .inl h => rw [h]; assumption
  | .inr ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩ =>
    rw [h₄]; rw [h₃] at al
    have : a ≠ c := fun h => (h ▸ pa).elim h₂
    simp [this] at al; simp [al]
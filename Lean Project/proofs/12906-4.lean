import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  have h1 : ∀ {l : List α}, length (filter p l) = countP p l := rfl
  have h2 : length (filter p l) = l.length ↔ ∀ a ∈ l, p a := by
    apply Iff.intro
    · intro h
      induction l with
      | nil => simp
      | cons hd tl ih =>
        simp at h
        have : hd ∈ filter p [hd] := by
          simp
          apply Mem.head
        simp [this] at h
        exact And.intro (by simp [h]) (ih (by simp [h]))
    · intro h
      induction l with
      | nil => simp
      | cons hd tl ih =>
        simp
        have : hd ∈ l := by simp
        have : hd ∈ filter p [hd] := by
          simp [h this]
          apply Mem.head
        simp [this, ih (h this)]
  rw [h1]
  exact h2

/- ACTUAL PROOF OF List.countP_eq_length -/

example : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countP_eq_length_filter, filter_length_eq_length]
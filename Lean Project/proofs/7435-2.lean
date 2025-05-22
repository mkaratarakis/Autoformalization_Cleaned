import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction l with
  | nil =>
    -- Base case: l is nil, which contradicts h : l ≠ []
    contradiction
  | cons y l ih =>
    -- Inductive step: l = y :: l
    simp [drop, length]
    cases l with
    | nil =>
      -- Case 1: l is nil
      simp [drop, length]
    | cons z l =>
      -- Case 2: l is not nil
      rw [← getLast_cons h]
      have hne : z :: l ≠ [] := by simp
      exact ih hne

/- ACTUAL PROOF OF List.drop_length_cons -/

example {l : List α} (h : l ≠ []) (a : α) :
    (a :: l).drop l.length = [l.getLast h] := by
  induction l generalizing a with
  | nil =>
    cases h rfl
  | cons y l ih =>
    simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [getLast_cons h₁]
    exact ih h₁ y
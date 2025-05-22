import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  induction n with
  | zero =>
    -- Base case: n = 0
    cases h
  | succ n ih =>
    -- Inductive step: n = succ n
    cases l with
    | nil =>
      -- Case 1: l is nil
      cases h
    | cons hd tl =>
      -- Case 2: l is cons hd tl
      cases m with
      | zero =>
        -- Subcase 1: m = 0
        rfl
      | succ m =>
        -- Subcase 2: m = succ m
        have h' : m < n := by
          apply Nat.lt_of_succ_lt_succ
          exact h
        simp only [take, List.get?]
        rw [ih h']

/- ACTUAL PROOF OF List.getElem?_take -/

example {l : List α} {n m : Nat} (h : m < n) : (l.take n)[m]? = l[m]? := by
  induction n generalizing l m with
  | zero =>
    exact absurd h (Nat.not_lt_of_le m.zero_le)
  | succ _ hn =>
    cases l with
    | nil => simp only [take_nil]
    | cons hd tl =>
      cases m
      · simp
      · simpa using hn (Nat.lt_of_succ_lt_succ h)
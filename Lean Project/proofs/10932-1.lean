import Init.Data.Nat.Linear
import Init.Data.List.BasicAux

open List


example (as bs : List α) (h : i < as.length) {h'} : (as ++ bs)[i] = as[i] := by
  induction as generalizing i
  case nil =>
    -- Base case: as = []
    -- The goal is to show that ([] ++ bs)[i] = [][i]
    -- Since the empty list has no elements, the index i must be out of bounds
    -- The goal is trivially true
    rfl
  case cons a as ih =>
    -- Inductive step: as = a :: as'
    -- We will use induction on the length of as
    cases i
    case zero =>
      -- Base case of induction: i = 0
      -- We need to show that (a :: as ++ bs)[0] = (a :: as)[0]
      -- By the definition of list concatenation and indexing, both sides of the equation are equal to a
      -- Therefore, the goal is trivially true due to the reflexive property of equality
      rfl
    case succ k =>
      -- Inductive step of induction: i = k + 1
      -- We need to show that (a :: as ++ bs)[k + 1] = (a :: as)[k + 1]
      -- By the induction hypothesis ih, it suffices to show that (as ++ bs)[k] = as[k]
      -- Since k < length(as) and k < length(as ++ bs), the induction hypothesis applies, and the goal is proved
      apply ih;
      simp [Nat.succ_lt_succ_iff] at h
      exact h

/- ACTUAL PROOF OF List.getElem_append_left -/

example (as bs : List α) (h : i < as.length) {h'} : (as ++ bs)[i] = as[i] := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => apply ih
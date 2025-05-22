import Init.Data.Nat.Linear
import Init.Data.List.BasicAux

open List


example (as bs cs : List α) : (as ++ bs = cs ++ bs) = (as = cs) := by
  apply propext
  constructor
  . intro h
    cases bs with
    | nil => exact h
    | cons b bs =>
      have h' := congrArg (· ++ b :: bs) h
      exact this bs h'
  . intro h
    rw [h]

/- ACTUAL PROOF OF List.append_cancel_right_eq -/

example (as bs cs : List α) : (as ++ bs = cs ++ bs) = (as = cs) := by
  apply propext; apply Iff.intro
  next => apply append_cancel_right
  next => intro h; simp [h]
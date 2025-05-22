import Init.Data.Nat.Linear
import Init.Data.List.BasicAux

open List



example (as bs : List α) (h : i < as.length) {h'} : (as ++ bs)[i] = as[i] := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => apply ih
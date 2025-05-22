import Init.Util
import Init.GetElem

open List


example (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rw [getElem]
  congr
  simp [Nat.succ]
  cases as with
  | nil =>
    simp [List.length, List.cons] at h
  | cons b bs =>
    simp [List.length, List.cons] at h
    rw [getElem]
    congr
    simp [Nat.succ]

/- ACTUAL PROOF OF List.getElem_cons_succ -/

example (a : α) (as : List α) (i : Nat) (h : i + 1 < (a :: as).length) : getElem (a :: as) (i+1) h = getElem as i (Nat.lt_of_succ_lt_succ h) := by
  rfl
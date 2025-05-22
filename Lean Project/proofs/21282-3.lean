import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example (p : α → Bool) (as bs : List α) :
    filterTR.loop p as bs = bs.reverse ++ filter p as := by
  induction as with
  | nil =>
    simp [filterTR.loop, filter]
  | cons a as ih =>
    simp [filterTR.loop, filter]
    by_cases hp : p a = true
    · simp [hp, ih]
      rw [List.reverse_cons, List.reverse_append]
      simp
    · simp [hp, ih]

/- ACTUAL PROOF OF List.filterTR_loop_eq -/

example (p : α → Bool) (as bs : List α) :
    filterTR.loop p as bs = bs.reverse ++ filter p as := by
  induction as generalizing bs with
  | nil => simp [filterTR.loop, filter]
  | cons a as ih =>
    simp only [filterTR.loop, filter]
    split <;> simp_all
import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @takeWhile = @takeWhileTR := by
  funext p l
  unfold takeWhileTR
  simp only [takeWhileTR.go, takeWhile]
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    generalize e : l = Array.mkEmpty.data ++ x :: xs
    apply ih
    simp
    by_cases h : p x
    · simp [h, Array.push]
    · simp [h, Array.push]

/- ACTUAL PROOF OF List.takeWhile_eq_takeWhileTR -/

example : @takeWhile = @takeWhileTR := by
  funext α p l; simp [takeWhileTR]
  suffices ∀ xs acc, l = acc.data ++ xs →
      takeWhileTR.go p l xs acc = acc.data ++ xs.takeWhile p from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc
  | nil => simp [takeWhile, takeWhileTR.go]
  | cons x xs IH =>
    simp only [takeWhileTR.go, Array.toList_eq, takeWhile]
    split
    · intro h; rw [IH] <;> simp_all
    · simp [*]
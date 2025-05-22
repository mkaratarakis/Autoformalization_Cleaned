import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @List.replace = @replaceTR := by
  funext α _ l b c
  induction' l with x xs ih generalizing b c
  · -- Base case
    simp only [replace, replaceTR, replaceTR.go, Array.nilToList]
  · -- Inductive step
    by_cases h : b == x
    · -- Case when b == x
      simp only [replace, h, replaceTR, replaceTR.go, Array.singletonToList, Array.push, Array.nilToList]
    · -- Case when b != x
      simp only [replace, h, replaceTR, replaceTR.go, Array.push, Array.nilToList, ih]
      simp only [Array.consToList, Array.singletonToList, ih]

/- ACTUAL PROOF OF List.replace_eq_replaceTR -/

example : @List.replace = @replaceTR := by
  funext α _ l b c; simp [replaceTR]
  suffices ∀ xs acc, l = acc.data ++ xs →
      replaceTR.go l b c xs acc = acc.data ++ xs.replace b c from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc
  | nil => simp [replace, replaceTR.go]
  | cons x xs IH =>
    simp only [replaceTR.go, Array.toListAppend_eq, replace]
    split
    · simp [*]
    · intro h; rw [IH] <;> simp_all
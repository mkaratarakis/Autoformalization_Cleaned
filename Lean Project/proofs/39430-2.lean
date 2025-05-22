import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @List.erase = @eraseTR := by
  funext l a
  induction l with
  | nil =>
    simp [erase, eraseTR]
  | cons x xs ih =>
    by_cases h : x == a
    · simp [h, erase, eraseTR]
    · simp [h, erase, eraseTR]
      rw [ih]
      simp [eraseTR.go, Array.push, Array.data]

/- ACTUAL PROOF OF List.erase_eq_eraseTR -/

example : @List.erase = @eraseTR := by
  funext α _ l a; simp [eraseTR]
  suffices ∀ xs acc, l = acc.data ++ xs → eraseTR.go l a xs acc = acc.data ++ xs.erase a from
    (this l #[] (by simp)).symm
  intro xs; induction xs with intro acc h
  | nil => simp [List.erase, eraseTR.go, h]
  | cons x xs IH =>
    simp only [eraseTR.go, Array.toListAppend_eq, List.erase]
    cases x == a
    · rw [IH] <;> simp_all
    · simp
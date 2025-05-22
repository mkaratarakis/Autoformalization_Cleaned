import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @List.erase = @eraseTR := by
  funext l a
  induction l with
  | nil =>
    simp [erase, eraseTR]
  | cons x xs ih =>
    cases h : Decidable (x == a) with
    | isTrue h =>
      simp [erase, eraseTR, h]
    | isFalse h =>
      simp [erase, eraseTR, h]
      rw [ih]
      simp [eraseTR.go, Array.push, Array.data]

  done

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
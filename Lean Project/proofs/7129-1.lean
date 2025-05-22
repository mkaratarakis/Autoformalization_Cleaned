import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @eraseIdx = @eraseIdxTR := by
  funext l n
  simp [eraseIdx, eraseIdxTR]
  unfold eraseIdxTR.go
  induction l generalizing n
  · intro acc h
    simp [h]
  · intro x xs IH acc h
    cases n <;> simp [h, eraseIdxTR.go]
    · simp [eraseIdxTR.go]
    · rw [← IH (acc.push x)]
      simp [Array.data_push, h]

/- ACTUAL PROOF OF List.eraseIdx_eq_eraseIdxTR -/

example : @eraseIdx = @eraseIdxTR := by
  funext α l n; simp [eraseIdxTR]
  suffices ∀ xs acc, l = acc.data ++ xs → eraseIdxTR.go l xs n acc = acc.data ++ xs.eraseIdx n from
    (this l #[] (by simp)).symm
  intro xs; induction xs generalizing n with intro acc h
  | nil => simp [eraseIdx, eraseIdxTR.go, h]
  | cons x xs IH =>
    match n with
    | 0 => simp [eraseIdx, eraseIdxTR.go]
    | n+1 =>
      simp only [eraseIdxTR.go, eraseIdx]
      rw [IH]; simp; simp; exact h
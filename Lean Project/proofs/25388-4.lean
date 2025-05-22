import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  intros m x y h_and h_or
  by_cases m_true : m = true
  · rw [m_true] at h_and h_or
    rw [h_and, Bool.true_and, Bool.true_and]
    exact h_or
  · rw [m_true] at h_and h_or
    rw [h_or, Bool.false_or, Bool.false_or]
    exact h_and

/- ACTUAL PROOF OF Bool.and_or_inj_left -/

example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  decide
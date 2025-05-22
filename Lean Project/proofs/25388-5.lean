import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  intros m x y h_and h_or
  by_cases m_true : m = true
  · rw [m_true] at h_and h_or
    exact h_and
  · rw [Bool.not_eq_false m_true] at h_and h_or
    exact h_or

/- ACTUAL PROOF OF Bool.and_or_inj_left -/

example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  decide
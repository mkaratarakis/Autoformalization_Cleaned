import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  intros m x y h_and h_or
  by_cases m_true : m = true
  · have : x = (m && x) := by rw [m_true, true_and]
    have : y = (m && y) := by rw [m_true, true_and]
    rw [h_and]
    exact this
  · have : m = false := by tauto
    have : x = (m || x) := by rw [this, false_or]
    have : y = (m || y) := by rw [this, false_or]
    rw [h_or]
    exact this

/- ACTUAL PROOF OF Bool.and_or_inj_left -/

example : ∀ {m x y : Bool}, (m && x) = (m && y) → (m || x) = (m || y) → x = y := by
  decide
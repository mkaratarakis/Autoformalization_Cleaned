import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  intros m x y h1 h2
  cases x <;> cases y <;> cases m
  · simp [and, or] at h1 h2
    exact h1
  · simp [and, or] at h1 h2
    exact h2
  · simp [and, or] at h1 h2
    apply h1
  · simp [and, or] at h1 h2
    apply h2

/- ACTUAL PROOF OF Bool.and_or_inj_right -/

example : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  decide
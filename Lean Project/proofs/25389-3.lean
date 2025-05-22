import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  intros m x y h1 h2
  cases x <;> cases y <;> cases m
  · simp [and, or] at h1 h2
    exact rfl
  · simp [and, or] at h1 h2
    exact False.elim (h1 rfl)
  · simp [and, or] at h1 h2
    exact False.elim (h1 rfl)
  · simp [and, or] at h1 h2
    exact rfl
  · simp [and, or] at h1 h2
    exact rfl
  · simp [and, or] at h1 h2
    exact False.elim (h2 rfl)
  · simp [and, or] at h1 h2
    exact False.elim (h2 rfl)
  · simp [and, or] at h1 h2
    exact rfl

/- ACTUAL PROOF OF Bool.and_or_inj_right -/

example : ∀ {m x y : Bool}, (x && m) = (y && m) → (x || m) = (y || m) → x = y := by
  decide
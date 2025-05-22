import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with
  | isTrue hp =>
    simp [decide, hp]
    exact Iff.intro
      (by intro htrue; rw [htrue]; exact hp)
      (by intro hp; rw [hp]; exact rfl)
  | isFalse hp =>
    simp [decide, hp]
    exact Iff.intro
      (by intro htrue; exfalso; rw [htrue] at hp; exact hp)
      (by intro hp; exfalso; exact hp)

/- ACTUAL PROOF OF true_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
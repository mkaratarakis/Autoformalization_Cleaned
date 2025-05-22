import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with
  | isTrue hp =>
    simp [decide, hp]
    apply Iff.intro
    · intro htrue
      rw [htrue]
      exact hp
    · intro hp
      rw [hp]
      exact rfl
  | isFalse hp =>
    simp [decide, hp]
    apply Iff.intro
    · intro htrue
      exfalso
      rw [htrue] at hp
      exact hp
    · intro hp
      exfalso
      exact hp

/- ACTUAL PROOF OF true_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
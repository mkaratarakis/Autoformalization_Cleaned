import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with
  | isTrue hp =>
    simp [decide, hp]
    exact Iff.intro
      (fun htrue => hp)
      (fun hp => rfl)
  | isFalse hp =>
    simp [decide, hp]
    exact Iff.intro
      (fun htrue => (hp (by rw [htrue])) )
      (fun hp => (hp rfl))

/- ACTUAL PROOF OF true_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
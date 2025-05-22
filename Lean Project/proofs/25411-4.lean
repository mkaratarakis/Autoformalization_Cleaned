import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with
  | isTrue hp =>
    simp [decide, hp]
    exact Iff.intro
      (fun htrue => by rw [htrue]; exact hp)
      (fun hp => by rw [hp]; exact rfl)
  | isFalse hp =>
    simp [decide, hp]
    exact Iff.intro
      (fun htrue => by exfalso; rw [htrue] at hp; exact hp)
      (fun hp => by exfalso; exact hp)

/- ACTUAL PROOF OF true_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
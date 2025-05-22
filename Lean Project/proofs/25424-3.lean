import Init.BinderPredicates
import Init.Data.Bool




example {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with
  | isTrue hp =>
    -- Case 1: p is true
    simp [decide]
    exact Iff.intro (fun h => False.elim h) (fun h => h hp)
  | isFalse hp =>
    -- Case 2: p is false
    simp [decide]
    exact Iff.intro (fun h => h ▸ rfl) (fun h => h ▸ rfl)

/- ACTUAL PROOF OF false_eq_decide_iff -/

example {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]
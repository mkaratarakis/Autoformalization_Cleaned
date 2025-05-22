import Init.BinderPredicates
import Init.Data.Bool





example {p : Prop} [h : Decidable p] : true = decide p ↔ p := by
  cases h with | _ q => simp [q]
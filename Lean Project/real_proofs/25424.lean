import Init.BinderPredicates
import Init.Data.Bool





example {p : Prop} [h : Decidable p] : false = decide p ↔ ¬p := by
  cases h with | _ q => simp [q]
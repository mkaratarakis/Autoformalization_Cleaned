import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  constructor
  · intro h
    cases l <;> cases l' <;> try {contradiction}
    all_goals {apply h; simp}
  · intro h
    cases h <;> cases l <;> cases l' <;> try {contradiction}
    all_goals {simp [zipWith]}

/- ACTUAL PROOF OF List.zipWith_eq_nil_iff -/

example {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp
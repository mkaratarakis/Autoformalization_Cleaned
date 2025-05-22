import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {k : Nat} : l.take k = [] ↔ k = 0 ∨ l = [] := by
  cases l <;> cases k <;> simp [take, List.take.eq_nil]
  all_goals constructor <;> try assumption
  all_goals {
    intros
    cases l <;> simp [take, List.take.eq_nil]
    all_goals constructor <;> try assumption
  }

/- ACTUAL PROOF OF List.take_eq_nil_iff -/

example {l : List α} {k : Nat} : l.take k = [] ↔ k = 0 ∨ l = [] := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]
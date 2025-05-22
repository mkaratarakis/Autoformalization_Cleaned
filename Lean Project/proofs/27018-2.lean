import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  have h₁ : some ((zipWithAll f as bs).head h) = some (f as.head? bs.head?) := by
    rw [head_eq_head?]
    have h₂ : (zipWithAll f as bs).head? = some (f as.head? bs.head?) := by
      cases h' : as <;> cases h'' : bs <;> simp [zipWithAll]
      · simp [zipWithAll]
      · simp [zipWithAll]
      · simp [zipWithAll]
      · simp [zipWithAll]
    exact h₂
  exact Option.some.inj h₁

/- ACTUAL PROOF OF List.head_zipWithAll -/

example {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWithAll]
  split <;> simp_all
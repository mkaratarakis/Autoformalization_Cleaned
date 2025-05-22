import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  have h₁ : some ((zipWithAll f as bs).head h) = some (f as.head? bs.head?) := by
    rw [head_eq_head?]
    cases h' : List.head? as
    · cases h'' : List.head? bs
      · simp [zipWithAll, h', h'']
      · simp [zipWithAll, h', h'']
    · cases h'' : List.head? bs
      · simp [zipWithAll, h', h'']
      · simp [zipWithAll, h', h'']
  exact Option.some.inj h₁

/- ACTUAL PROOF OF List.head_zipWithAll -/

example {f : Option α → Option β → γ} (h) :
    (zipWithAll f as bs).head h = f as.head? bs.head? := by
  apply Option.some.inj
  rw [← head?_eq_head, head?_zipWithAll]
  split <;> simp_all
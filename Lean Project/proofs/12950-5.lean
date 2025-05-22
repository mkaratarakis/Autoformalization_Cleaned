import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example (l) : countP.go p l n = n + countP.go p l 0 := by
  induction l with
  | nil =>
    simp [countP.go]
  | cons head tail ih =>
    cases hp : p head <;> simp [countP.go, ih]
    · calc
        countP.go p (head :: tail) n
          = countP.go p tail (n + 1) := by
              rw [countP.go]
              apply Bool.bif_true hp
        _ = n + 1 + countP.go p tail 0 := by rw [ih]
        _ = n + (1 + countP.go p tail 0) := by rfl
        _ = n + countP.go p (head :: tail) 0 := by
              rw [countP.go]
              apply Bool.bif_true hp
    · calc
        countP.go p (head :: tail) n
          = n + countP.go p tail 0 := by
              rw [countP.go]
              apply Bool.bif_false hp
        _ = n + countP.go p (head :: tail) 0 := by
              rw [countP.go]
              apply Bool.bif_false hp

/- ACTUAL PROOF OF List.countP_go_eq_add -/

example (l) : countP.go p l n = n + countP.go p l 0 := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    unfold countP.go
    rw [ih (n := n + 1), ih (n := n), ih (n := 1)]
    if h : p head then simp [h, Nat.add_assoc] else simp [h]
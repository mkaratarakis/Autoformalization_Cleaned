import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)

example (l) (pa : p a) : countP p (a :: l) = countP p l + 1 := by
  have : countP.go p (a :: l) 0 = countP.go p l 1 :=
  by
    simp [countP.go, pa]
  rw [countP]
  rw [this]
  rw [countP.go]
  rfl

/- ACTUAL PROOF OF List.countP_cons_of_pos -/

example (l) (pa : p a) : countP p (a :: l) = countP p l + 1 := by
  have : countP.go p (a :: l) 0 = countP.go p l 1 := show cond .. = _ by rw [pa]; rfl
  unfold countP
  rw [this, Nat.add_comm, List.countP_go_eq_add]
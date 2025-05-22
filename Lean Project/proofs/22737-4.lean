import Init.SizeOf
import Init.Data.Nat.Basic
import Init.WF

open WellFounded
variable {α : Sort u} {r : α → α → Prop}
variable {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r)
variable {C : α → Sort v}
variable (F : ∀ x, (∀ y, r y x → C y) → C x)
variable (F : ∀ x, (∀ y, r y x → C y) → C x)

example (x : α) (acx : Acc r x) : fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) := by
  rfl

/- ACTUAL PROOF OF WellFounded.fixFEq -/

example (x : α) (acx : Acc r x) : fixF F x acx = F x (fun (y : α) (p : r y x) => fixF F y (Acc.inv acx p)) := by
  induction acx with
  | intro x r _ => exact rfl
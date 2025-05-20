import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Basic

open MvQPF
open MvFunctor
variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]
open MvFunctor (LiftP LiftR)

example {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← q.abs_repr]
  rw [MvQPF.abs_map q (TypeVec.id : α ⟹ α)]
  rw [MvPFunctor.id_map q.P]
  rw [q.abs_repr]

/- ACTUAL PROOF OF MvQPF.id_map -/

example {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x, ← abs_map]
  rfl
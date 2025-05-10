import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Basic

open MvQPF
open MvFunctor
variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]
open MvFunctor (LiftP LiftR)


example {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x, ← abs_map, ← abs_map, ← abs_map]
  rfl
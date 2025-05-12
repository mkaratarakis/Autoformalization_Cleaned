import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Basic

open MvQPF
open MvFunctor
variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]
open MvFunctor (LiftP LiftR)
open Set
open MvFunctor (LiftP LiftR)

example {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ := by
  constructor
  · intro h a f hx
    apply h
    exact ⟨a, f, hx, fun j => mem_univ _⟩
  · intro h a f hxf
    exact h _ _ hxf

/- ACTUAL PROOF OF MvQPF.mem_supp -/

example {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u ∈ f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  intro h p; rw [liftP_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
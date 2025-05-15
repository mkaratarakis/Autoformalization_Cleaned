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
  unfold supp
  constructor
  · intro h a f hab
    apply h
    · use a, f
      exact hab
    · intro j
      exact mem_image_of_mem _ (mem_univ _)
  · intro h P hx a f hab
    apply hx
    · use a, fun i j => ⟨f i j, h _ _ hab⟩
      exact hab.symm
    · intro i j
      exact (h _ _ hab).1
    · intro i j
      exact (h _ _ hab).2

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
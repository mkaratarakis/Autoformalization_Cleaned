import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Push

open Quiver
open Push
variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)
variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

example (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  apply Prefunctor.ext
  · exact Φ₀
  · intros X Y f
    simp only [Prefunctor.comp_map, Prefunctor.id_map, lift_obj, lift_comp, Prefunctor.comp_obj]
    have h1 : ∀ (X : V), τ (σ X) = φ.obj X := by
      intro X
      rw [h]
    have h2 : Φ.map f = PushQuiver.rec (fun X' Y' _ => τ X' ⟶ τ Y') (fun X' Y' f => φ.map f) f := by
      apply Eq.symm
      apply eq_of_heq
      iterate 2 apply (cast_heq _ _).trans
      apply HEq.symm
      apply (eqRec_heq _ _).trans
      have : ∀ {α γ} {β : α → γ → Sort _} {a a'} (p : a = a') g (b : β a g), HEq (p ▸ b) b := by
        intros
        subst_vars
        rfl
      apply this
    rw [h2]
    exact eq_of_heq (heq_of_homOfEq_ext (h X) (h Y) (h2.symm))

/- ACTUAL PROOF OF Quiver.Push.lift_unique -/

example (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map, cast_eq]
    rfl
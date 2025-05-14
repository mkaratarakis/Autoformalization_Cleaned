import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Quiver.Push

open Quiver
open Push
variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)
variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

example (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  -- Show that the object mapping of Φ is equal to τ
  apply Prefunctor.ext
  { exact Φ₀ }
  -- Show that the arrow mapping of Φ is defined by the recursion principle on the pushed quiver
  intros X Y f
  simp only [lift, Prefunctor.id_obj, Prefunctor.id_map, Prefunctor.comp_map,
    Quiver.Hom.push_of_map, Eq.recOn_eq, Φcomp.map, Φ₀]
  exact id

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
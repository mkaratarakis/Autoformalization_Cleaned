import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology

open CategoryTheory
open coherentTopology
variable {C : Type*} [Category C] [Precoherent C] {X : C}


example (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) →
        (S ∈ (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h ↦ by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Bimon_

open Bimon_
open CategoryTheory MonoidalCategory
variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]
variable {C}

example (M : Bimon_ C) :
    M.X.mul ≫ M.counit.hom = (M.counit.hom ⊗ M.counit.hom) ≫ (λ_ _).hom := by
  rw [λ_]
  simp only [counit_tensor_id, id_comp, comp_id]

/- ACTUAL PROOF OF Bimon_.mul_counit -/

example (M : Bimon_ C) :
    M.X.mul ≫ M.counit.hom = (M.counit.hom ⊗ M.counit.hom) ≫ (λ_ _).hom := by
  simp
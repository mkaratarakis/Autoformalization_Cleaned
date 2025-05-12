import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

open SheafOfModules
open CategoryTheory Limits
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
variable {I J : Type u} (f : I → J)

example (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp only [freeSection, freeMap, sectionsMap, freeHomEquiv_symm_comp, 𝟙_comp]
  rfl

/- ACTUAL PROOF OF SheafOfModules.sectionMap_freeMap_freeSection -/

example (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]
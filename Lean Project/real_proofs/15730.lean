import Mathlib.Analysis.NormedSpace.ConformalLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Conformal.NormedSpace

open ConformalAt
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]
open LinearIsometry ContinuousLinearMap


example {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩
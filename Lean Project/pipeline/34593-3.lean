import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f g : E → F} {f' g' : E →L[𝕜] F} {x : E} {s : Set E} {L : Filter E}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/


variable (x)
example {g : F → G} {g' : F →L[𝕜] G} {L' : Filter F}
    (hg : HasFDerivAtFilter g g' (f x) L') (hf : HasFDerivAtFilter f f' x L) (hL : Tendsto f L L') :
HasFDerivAtFilter (g ∘ f) (g'.comp f') x L := by
  -- Define the auxiliary function `k`
  let k := fun x' => g (f x') - g (f x) - g' (f x' - f x)

  -- Step 1: Show that `g' (f x' - f x) - g'.comp f' (x' - x)` is little-o of `x' - x`
  have eq₁ : (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =o[L] fun x' => x' - x := by
    refine' ((hf.isLittleO.congr_right_of_sub_eq_zero fun _ => sub_add_cancel _ _).trans_isBigO _).trans_isLittleO _
    · exact (g'.isBigO_sub _ _)
    · refine' g'.isBigO_sub_rev.trans_isBigO _
      exact hf.isBigO_sub

  -- Step 2: Show that `k ∘ f - (g'.comp f' (x' - x))` is little-o of `x' - x`
  have eq₂ : (fun x' => k (f x') - g'.comp f' (x' - x)) =o[L] fun x' => x' - x := by
    refine' (IsLittleO.comp_tendsto _ hL).add_isLittleO eq₁
    exact hg.isLittleO

  -- Conclusion: Show that `g ∘ f` has a Fréchet derivative `g'.comp f'` at `x` along `L`
  exact .of_isLittleOTVS <| by rwa [sub_sub_sub_cancel_right]

/- ACTUAL PROOF OF HasFDerivAtFilter.comp -/

example {g : F → G} {g' : F →L[𝕜] G} {L' : Filter F}
    (hg : HasFDerivAtFilter g g' (f x) L') (hf : HasFDerivAtFilter f f' x L) (hL : Tendsto f L L') :
    HasFDerivAtFilter (g ∘ f) (g'.comp f') x L := by
  let eq₁ := (g'.isBigO_comp _ _).trans_isLittleO hf.isLittleO
  let eq₂ := (hg.isLittleO.comp_tendsto hL).trans_isBigO hf.isBigO_sub
  refine .of_isLittleO <| eq₂.triangle <| eq₁.congr_left fun x' => ?_
  simp
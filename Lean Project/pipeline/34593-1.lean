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
    -- Use the Fréchet derivative property of `f` and the continuity of `g'`
    refine' (hg.isBigO_sub.comp (hf.isLittleO.add_isBigO (g'.isBigO_sub _ _))).trans_isLittleO _
    -- Apply the transitivity of little-o and big-O notations
    letI : NormOneClass F := NormedAddCommGroup.toNormOneClass
    exact isBigO_one.isLittleO_of_tendsto (IsLittleO.of_le_id hL)

  -- Step 2: Show that `k ∘ f - (g'.comp f' (x' - x))` is little-o of `x' - x`
  have eq₂ : (fun x' => k (f x') - g'.comp f' (x' - x)) =o[L] fun x' => x' - x := by
    -- Apply the transitivity of little-o notations
    refine' ((hg.isLittleO.comp_tendsto hL).add_isLittleO eq₁).congr_left _
    -- Simplify the expression
    ext
    simp only [sub_add_cancel, Pi.sub_apply, Function.comp_app, sub_self]

  -- Conclusion: Show that `g ∘ f` has a Fréchet derivative `g'.comp f'` at `x` along `L`
  exact .of_isLittleOTVS <| by rwa [sub_sub_sub_cancel_right]


6. **Error Message**
```
failed to synthesize type class instance for
𝕜 : Type u_1,
_inst_1 : NontriviallyNormedField 𝕜,
E : Type u_2,
_inst_2 : NormedAddCommGroup E,
_inst_3 : NormedSpace 𝕜 E,
F : Type u_3,
_inst_4 : NormedAddCommGroup F,
_inst_5 : NormedSpace 𝕜 F,
G : Type u_4,
_inst_6 : NormedAddCommGroup G,
_inst_7 : NormedSpace 𝕜 G,
G' : Type u_5,
_inst_8 : NormedAddCommGroup G',
_inst_9 : NormedSpace 𝕜 G',
f g : E → F,
f' g' : E →L[𝕜] F,
x : E,
s : Set E,
L : Filter E,
g' : F →L[𝕜] G,
L' : Filter F,
hg : HasFDerivAtFilter g g' (f x) L',
hf : HasFDerivAtFilter f f' x L,
hL : Tendsto f L L',
k : E → G
⊢ HasOpr 𝕜 G'
```
To resolve the error, we need to adjust the proof to ensure that the type class instance for `HasOpr 𝕜 G'` is correctly synthesized. This can be achieved by explicitly stating the required type class instances and ensuring that all necessary imports are included.

Let's continue the proof by addressing the error and completing the formal proof:

```lean
-- Define the auxiliary function `k`
let k := fun x' => g (f x') - g (f x) - g' (f x' - f x)

-- Step 1: Show that `g' (f x' - f x) - g'.comp f' (x' - x)` is little-o of `x' - x`
have eq₁ : (fun x' => g' (f x' - f x) - g'.comp f' (x' - x)) =o[L] fun x' => x' - x := by
  -- Use the Fréchet derivative property of `f` and the continuity of `g'`
  refine' (hg.isBigO_sub.comp (hf.isLittleO.add_isBigO (g'.isBigO_sub _ _))).trans_isLittleO _
  -- Apply the transitivity of little-o and big-O notations
  letI : NormOneClass F := NormedAddCommGroup.toNormOneClass
  exact isBigO_one.isLittleO_of_tendsto (IsLittleO.of_le_id hL)

-- Step 2: Show that `k ∘ f - (g'.comp f' (x' - x))` is little-o of `x' - x`
have eq₂ : (fun x' => k (f x') - g'.comp f' (x' - x)) =o[L] fun x' => x' - x := by
  -- Apply the transitivity of little-o notations
  refine' ((hg.isLittleO.comp_tendsto hL).add_isLittleO eq₁).congr_left _
  -- Simplify the expression
  ext
  simp only [sub_add_cancel, Pi.sub_apply, Function.comp_app, sub_self]

-- Conclusion: Show that `g ∘ f` has a Fréchet derivative `g'.comp f'` at `x` along `L`
exact .of_isLittleOTVS <| by rwa [sub_sub_sub_cancel_right]
```

/- ACTUAL PROOF OF HasFDerivAtFilter.comp -/

example {g : F → G} {g' : F →L[𝕜] G} {L' : Filter F}
    (hg : HasFDerivAtFilter g g' (f x) L') (hf : HasFDerivAtFilter f f' x L) (hL : Tendsto f L L') :
    HasFDerivAtFilter (g ∘ f) (g'.comp f') x L := by
  let eq₁ := (g'.isBigO_comp _ _).trans_isLittleO hf.isLittleO
  let eq₂ := (hg.isLittleO.comp_tendsto hL).trans_isBigO hf.isBigO_sub
  refine .of_isLittleO <| eq₂.triangle <| eq₁.congr_left fun x' => ?_
  simp
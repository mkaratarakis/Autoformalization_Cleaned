import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Comp

open HasStrictDerivAt
open scoped Classical Topology Filter ENNReal
open Filter Asymptotics Set
open ContinuousLinearMap (smulRight smulRight_one_eq_iff)
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {f f₀ f₁ g : 𝕜 → F}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {f' f₀' f₁' g' : F}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {x : 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {s t : Set 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {L L₁ L₂ : Filter 𝕜}
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {s' t' : Set 𝕜'} {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'}
  {h₁' : 𝕜} {g₁ : 𝕜' → F} {g₁' : F} {L' : Filter 𝕜'} {y : 𝕜'} (x)

example (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  -- 1. We know that \( h_2 \circ h \) and \( h_2 \circ (h x) \) are differentiable at \( x \) and \( h(x) \) respectively.
  -- 2. We need to show \( (h₂ ∘ h)'(x) = h₂'(h(x)) \cdot h'(x) \).

  -- By the chain rule, the derivative of \( h_2 \circ h \) at \( x \) is given by:
  -- \((h_2 \circ h)'(x) = h_2'(h(x)) \cdot h'(x)\).

  -- Since multiplication in a commutative magma is commutative, we have:
  -- \(h_2'(h(x)) \cdot h'(x) = h'(x) \cdot h_2'(h(x))\).

  -- Therefore, we can rewrite the goal to show that the derivative of \( h_2 \circ h \) at \( x \) is:
  -- \( h'(x) \cdot h_2'(h(x)) \).

  exact (hh.restrictScalars 𝕜).comp_hasStrictDerivAt x (hh₂.restrictScalars 𝕜)

/- ACTUAL PROOF OF HasStrictDerivAt.comp -/

example (hh₂ : HasStrictDerivAt h₂ h₂' (h x)) (hh : HasStrictDerivAt h h' x) :
    HasStrictDerivAt (h₂ ∘ h) (h₂' * h') x := by
  rw [mul_comm]
  exact hh₂.scomp x hh
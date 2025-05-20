import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Intrinsic

open IsClosed
open AffineSubspace Set
open scoped Pointwise
variable {𝕜 V W Q P : Type*}
variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}
variable {𝕜}

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  have h : (↑) '' ((↑) ⁻¹' s) = s := by
    ext y
    simp
  rw [intrinsicClosure, ← h, hs.closure_eq]
  simp

/- ACTUAL PROOF OF IsClosed.intrinsicClosure -/

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset
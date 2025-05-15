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
  apply le_antisymm
  · exact intrinsicClosure_subset 𝕜 s
  · rw [intrinsicClosure, ← image_univ, ← image_preimage_eq_inter_range]
    exact subset_preimage_image _ _
    apply image_subset_range
    rw [← @closure_minimal _ _ _ _ ((↑) ⁻¹' s) hs]
    exact subset_closure

/- ACTUAL PROOF OF IsClosed.intrinsicClosure -/

example (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Intrinsic


open AffineSubspace Set
open scoped Pointwise
variable {𝕜 V W Q P : Type*}
variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}
variable {𝕜}

example : intrinsicFrontier 𝕜 (∅ : Set P) = ∅ := by
  rw [intrinsicFrontier, image_empty]
  exact frontier_empty

/- ACTUAL PROOF OF intrinsicFrontier_empty -/

example : intrinsicFrontier 𝕜 (∅ : Set P) = ∅ := by
  simp [intrinsicFrontier]
import Mathlib.Topology.Basic
import Mathlib.Topology.NhdsSet


open Set Filter Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}


example : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by
  simp [nhdsSet]
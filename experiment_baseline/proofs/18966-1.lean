import Mathlib.Topology.Basic
import Mathlib.Topology.NhdsSet


open Set Filter Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Filter X}
  {s t s₁ s₂ t₁ t₂ : Set X} {x : X}

example : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by
  unfold nhdsSet
  rw [iSup_le_iff]
  exact forall_congr' (fun x => forall_congr' (fun hx : x ∈ s => by simp [hx]))

/- ACTUAL PROOF OF nhdsSet_le -/

example : 𝓝ˢ s ≤ f ↔ ∀ x ∈ s, 𝓝 x ≤ f := by
  simp [nhdsSet]
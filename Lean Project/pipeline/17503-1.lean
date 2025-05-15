import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.GroupTheory.Subgroup.Centralizer

open Subgroup
variable {G : Type*} [Group G]
variable {H K : Subgroup G}

example {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  rw [mem_centralizer_iff]
  exact forall_congr' fun h => by rw [← mul_inv_eq_iff_eq_mul, inv_inv, ← mul_assoc, ← mul_assoc]

/- ACTUAL PROOF OF Subgroup.mem_centralizer_iff_commutator_eq_one -/

example {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, h * g * h⁻¹ * g⁻¹ = 1 := by
  simp only [mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]
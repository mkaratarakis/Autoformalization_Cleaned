import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Subgroup.Centralizer


assert_not_exists Cardinal Multiset Ring

variable {G G' F : Type*} [Group G] [Group G'] [FunLike F G G'] [MonoidHomClass F G G']

namespace Subgroup

instance commutator : Bracket (Subgroup G) (Subgroup G) :=
  ⟨fun H₁ H₂ => closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g }⟩

theorem commutator_def (H₁ H₂ : Subgroup G) :
    ⁅H₁, H₂⁆ = closure { g | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g } :=
  rfl

variable {g₁ g₂ g₃} {H₁ H₂ H₃ K₁ K₂ : Subgroup G}

/- Recall that the commutator is defined as the closure of the set {g | ∃ g₁ ∈  H₁, ∃ g₂ ∈  H₂, ⁅g₁,g₂⁆ = g}.
    Because a set is a subset of its closure, it would to show that ⁅g₁,g₂⁆ ∈ {g | ∃ g₁ ∈  H₁, ∃ g₂ ∈  H₂, ⁅g₁,g₂⁆ = g}.
    g₁ and g₂ are the elements we need. -/

theorem commutator_mem_commutator (h₁ : g₁ ∈ H₁) (h₂ : g₂ ∈ H₂) : ⁅g₁, g₂⁆ ∈ ⁅H₁, H₂⁆ := by
  apply subset_closure
  simp
  use g₁
  constructor
  · exact h₁
  · use g₂

#check H₃.closure_le.trans

theorem commutator_le : ⁅H₁, H₂⁆ ≤ H₃ ↔ ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, ⁅g₁, g₂⁆ ∈ H₃ := by
    constructor
    · intro h

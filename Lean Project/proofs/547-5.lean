import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} {l : List α} :
    l.erase a = l' ↔
      (a ∉ l ∧ l = l') ∨
        ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ := by
  constructor
  · intro h
    by_cases h₁ : a ∈ l
    · have h₂ : ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ := by
        let rec splitList : List α → Option ((List α) × (List α))
          | [] => none
          | x :: xs =>
            if hx : x == a then some ([], xs)
            else match splitList xs with
            | none => none
            | some (l₁, l₂) => some (x :: l₁, l₂)
        have : splitList l ≠ none := by
          simp [splitList, h₁]
        obtain ⟨l₁, l₂⟩ := Option.get (splitList l) this
        exists l₁, l₂
        constructor
        · intro h₃
          apply List.not_mem_of_not_mem_append_right
          intro h₄
          apply h₁
          rw [List.mem_cons_eq] at h₄
          exact h₄.2
        · rw [List.erase_eq_append_of_pos] at h
          exact h
    · left
      constructor
      · exact h₁
      · apply List.erase_of_not_mem h₁

  · intro h
    cases h
    · apply List.erase_of_not_mem h.1
    · obtain ⟨l₁, l₂, hl⟩ := h
      rw [List.erase_eq_append_of_pos]
      · apply List.not_mem_of_not_mem_append_right
        intro h₄
        apply hl.1
        rw [List.mem_cons_eq] at h₄
        exact h₄.2
      · exact hl.2.2

/- ACTUAL PROOF OF List.erase_eq_iff -/

example [LawfulBEq α] {a : α} {l : List α} :
    l.erase a = l' ↔
      (a ∉ l ∧ l = l') ∨
        ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l' = l₁ ++ l₂ := by
  rw [erase_eq_eraseP', eraseP_eq_iff]
  simp only [beq_iff_eq, forall_mem_ne', exists_and_left]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨a', l', h, rfl, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨l', h, x, by simp⟩
  · rintro (⟨h, rfl⟩ | ⟨l₁, h, x, rfl, rfl⟩)
    · left; simp_all
    · right; refine ⟨a, l₁, h, by simp⟩
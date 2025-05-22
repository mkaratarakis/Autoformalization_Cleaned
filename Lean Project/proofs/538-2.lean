import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nat
variable [BEq α]

example [LawfulBEq α] (a b : α) (l : List α) :
    (l.erase a).erase b = (l.erase b).erase a := by
  by_cases h : a = b
  · subst h
    rfl
  by_cases h' : a ∈ l
  · by_cases h'' : b ∈ l
    · have h₁ : l = l₀ ++ [a] ++ l₁ ∧ b ∈ l₀ := by
        apply And.intro
        · exact List.mem_split h'
        · apply List.mem_of_mem_erase
          exact h''
      have h₂ : l = l₂ ++ [b] ++ l₃ ∧ a ∈ l₂ := by
        apply And.intro
        · exact List.mem_split h''
        · apply List.mem_of_mem_erase
          exact h'
      let ⟨l₀, l₁, rfl⟩ := h₁
      let ⟨l₂, l₃, rfl⟩ := h₂
      simp only [erase, append_assoc, h₁, h₂, Ne.def, not_false_iff,
        erase_append_right, erase_append_right]
    · simp [h'']
  · simp [h']

/- ACTUAL PROOF OF List.erase_comm -/

example [LawfulBEq α] (a b : α) (l : List α) :
    (l.erase a).erase b = (l.erase b).erase a := by
  if ab : a == b then rw [eq_of_beq ab] else ?_
  if ha : a ∈ l then ?_ else
    simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]
  if hb : b ∈ l then ?_ else
    simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
  match l, l.erase a, exists_erase_eq ha with
  | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩ =>
    if h₁ : b ∈ l₁ then
      rw [erase_append_left _ h₁, erase_append_left _ h₁,
          erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
    else
      rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
          erase_cons_tail ab, erase_cons_head]
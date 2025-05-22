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
    · induction l generalizing a b
      · simp only [List.erase, nil_append, eq_self_iff_true,
                   ite_true, and_false]
      · case pos.cons._@.tmp._hyg.114._matchₓ x xs ih =>
        by_cases h₁ : x = a
        · subst h₁
          simp only [List.erase, true_and, eq_self_iff_true,
                     ite_true, cons_append, Ne.def, not_false_iff]
          rw [ih]
        · by_cases h₂ : x = b
          · subst h₂
            simp only [List.erase, false_and, eq_self_iff_true,
                       ite_false, cons_append, Ne.def, not_false_iff]
            rw [ih]
          · simp only [List.erase, false_and, ne_eq, ite_false,
                       cons_append, Ne.def, not_false_iff]
            rw [ih]
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
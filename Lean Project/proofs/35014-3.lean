API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.suffix_cons_iff -/

example : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ := by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃
      injection hl₃ with _ hl₄
      exact Or.inr ⟨_, hl₄⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)
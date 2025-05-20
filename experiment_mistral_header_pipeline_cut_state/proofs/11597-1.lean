API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF intrinsicInterior_empty -/

example : intrinsicInterior 𝕜 (∅ : Set P) = ∅ := by
  simp [intrinsicInterior]
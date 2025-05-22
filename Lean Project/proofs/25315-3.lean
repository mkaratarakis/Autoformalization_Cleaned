API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.or_eq_true_iff -/

example : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by
  simp
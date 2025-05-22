API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.or_eq_true_iff -/

example : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by
  simp
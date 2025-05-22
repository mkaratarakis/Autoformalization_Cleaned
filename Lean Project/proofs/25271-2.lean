API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.eq_false_or_eq_true -/

example : (b : Bool) → b = true ∨ b = false := by
  decide
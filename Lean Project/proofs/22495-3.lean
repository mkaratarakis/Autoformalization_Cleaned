API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.atLeastTwo_true_right -/

example : atLeastTwo a b true  = (a || b) := by
  cases a <;> cases b <;> simp [atLeastTwo]
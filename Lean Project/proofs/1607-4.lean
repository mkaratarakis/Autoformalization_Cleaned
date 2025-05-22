API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.length_iota -/

example (n : Nat) : length (iota n) = n := by
  simp [iota_eq_reverse_range']
API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.pairwise_lt_range -/

example (n : Nat) : Pairwise (· < ·) (range n) := by
  simp (config := {decide := true}) only [range_eq_range', pairwise_lt_range']
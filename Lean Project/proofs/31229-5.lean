API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Nat.zero_sub -/

example (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, Nat.sub_succ]; decide
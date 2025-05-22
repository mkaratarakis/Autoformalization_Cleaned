API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.length_iota -/

example (n : Nat) : length (iota n) = n := by
  simp [iota_eq_reverse_range']
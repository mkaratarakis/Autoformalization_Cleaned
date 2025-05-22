API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Nat.add_div_left -/

example (x : Nat) {z : Nat} (H : 0 < z) : (z + x) / z = (x / z) + 1 := by
  rw [Nat.add_comm, add_div_right x H]
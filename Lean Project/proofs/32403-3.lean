API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Nat.add_sub_cancel' -/

example {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]
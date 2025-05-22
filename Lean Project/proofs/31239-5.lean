API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Nat.mul_sub_one -/

example (n m : Nat) : n * (m - 1) = n * m - n := by
  rw [Nat.mul_comm, Nat.sub_one_mul , Nat.mul_comm]
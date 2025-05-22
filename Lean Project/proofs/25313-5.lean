API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.iff_self_and -/

example : ∀(a b : Bool), (a = (a && b)) ↔ (a → b) := by
  decide
API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide
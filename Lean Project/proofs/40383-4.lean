API ERROR: API error occurred: Status 429
{"object":"error","message":"Service tier capacity exceeded for this model.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.reverseAux_reverseAux -/

example (as bs cs : List α) : reverseAux (reverseAux as bs) cs = reverseAux bs (reverseAux (reverseAux as []) cs) := by
  induction as generalizing bs cs with
  | nil => rfl
  | cons a as ih => simp [reverseAux, ih (a::bs), ih [a]]
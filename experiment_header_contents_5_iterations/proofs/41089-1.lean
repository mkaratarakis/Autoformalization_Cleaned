API ERROR: API error occurred: Status 504
{
  "message":"The upstream server is timing out",
  "request_id":"cb7b2f341f8d4b2d9292031192a8cb39"
}

/- ACTUAL PROOF OF HasStrictDerivAt.mul -/

example (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x) :
    HasStrictDerivAt (fun y => c y * d y) (c' * d x + c x * d') x := by
  have := (HasStrictFDerivAt.mul' hc hd).hasStrictDerivAt
  rwa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul, one_smul,
    add_comm] at this
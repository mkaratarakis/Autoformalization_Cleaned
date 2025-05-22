import Init.Core
import Init.SimpLemmas




example {_ : Decidable b} [Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h₁ : b = c)
    (h₂ : (h : c)  → x (h₁.mpr_prop h) = u h)
    (h₃ : (h : ¬c) → y (h₁.mpr_not h)  = v h) :
    dite b x y = dite c u v := by
  cases h₁
  case inl hc =>
    apply dite_true_iff_left
    intro h
    rw [hc]
    exact h₂ h
  case inr hnc =>
    apply dite_false_iff_right
    intro h
    rw [hnc]
    exact h₃ h

/- ACTUAL PROOF OF dite_congr -/

example {_ : Decidable b} [Decidable c]
    {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}
    (h₁ : b = c)
    (h₂ : (h : c)  → x (h₁.mpr_prop h) = u h)
    (h₃ : (h : ¬c) → y (h₁.mpr_not h)  = v h) :
    dite b x y = dite c u v := by
  cases Decidable.em c with
  | inl h => rw [dif_pos h]; subst b; rw [dif_pos h]; exact h₂ h
  | inr h => rw [dif_neg h]; subst b; rw [dif_neg h]; exact h₃ h
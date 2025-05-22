import Init.PropLemmas
import Init.Data.Fin.Basic
import Init.Data.Fin.Iterate

open Fin


example {P : Nat → Sort _} (state : ∀(i : Nat), P i)
    {n : Nat} (f : ∀(i : Fin n), P i.val → P (i.val+1)) (s : P 0)
    (init : s = state 0)
    (step : ∀(i : Fin n), f i (state i) = state (i+1)) :
    hIterate P s f = state n := by
  apply hIterate_eq
  · exact init
  · intros i s' h
    rw [← h]
    exact step i

/- ACTUAL PROOF OF Fin.hIterate_eq -/

example {P : Nat → Sort _} (state : ∀(i : Nat), P i)
    {n : Nat} (f : ∀(i : Fin n), P i.val → P (i.val+1)) (s : P 0)
    (init : s = state 0)
    (step : ∀(i : Fin n), f i (state i) = state (i+1)) :
    hIterate P s f = state n := by
  apply hIterate_elim (fun i s => s = state i) f s init
  intro i s s_eq
  simp only [s_eq, step]
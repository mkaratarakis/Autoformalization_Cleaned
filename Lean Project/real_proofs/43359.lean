import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Expr
open Linear (Var hugeFuel Context Var.denote)


example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    simp [eq_of_beq h]
  | var v => simp!
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]
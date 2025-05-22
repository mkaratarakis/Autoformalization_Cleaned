import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Expr
open Linear (Var hugeFuel Context Var.denote)

example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e using Expr.recOn
  case mul a b ih_a ih_b =>
    show denote ctx (Expr.mul a b).toPoly = denote ctx (Expr.mul a b)
    rw [Expr.toPoly_mul]
    rw [denote_mul]
    rw [ih_a, ih_b]
  case const k =>
    show denote ctx (Expr.const k).toPoly = denote ctx (Expr.const k)
    cases k
    case zero =>
      show denote ctx (Expr.const 0).toPoly = denote ctx (Expr.const 0)
      rfl
    case succ _ =>
      show denote ctx (Expr.const (succ k)).toPoly = denote ctx (Expr.const (succ k))
      rfl
  case var v =>
    show denote ctx (Expr.var v).toPoly = denote ctx (Expr.var v)
    rfl
  case add a b ih_a ih_b =>
    show denote ctx (Expr.add a b).toPoly = denote ctx (Expr.add a b)
    rw [Expr.toPoly_add]
    rw [denote_add]
    rw [ih_a, ih_b]

/- ACTUAL PROOF OF Nat.SOM.Expr.toPoly_denote -/

example (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    simp [eq_of_beq h]
  | var v => simp!
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]
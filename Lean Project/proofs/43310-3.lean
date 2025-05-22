import Init.Data.Nat.Linear
import Init.Data.List.BasicAux
import Init.Data.Nat.SOM

open Nat
open SOM
open Poly
open Linear (Var hugeFuel Context Var.denote)

example (ctx : Context) (p : Poly) (k : Nat) (m : Mon) : (p.mulMon k m).denote ctx = p.denote ctx * k * m.denote ctx := by
  unfold mulMon
  unfold denote
  simp
  induction p with
  | nil => simp
  | cons p_hd p_tl p_IH =>
    simp
    rw [p_IH]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

/- ACTUAL PROOF OF Nat.SOM.Poly.mulMon_denote -/

example (ctx : Context) (p : Poly) (k : Nat) (m : Mon) : (p.mulMon k m).denote ctx = p.denote ctx * k * m.denote ctx := by
  simp [mulMon, go]; simp!
where
  go (p : Poly) (acc : Poly) : (mulMon.go k m p acc).denote ctx = acc.denote ctx + p.denote ctx * k * m.denote ctx := by
   match p with
   | [] => simp!
   | (k', m') :: p =>
     simp! [go p, Nat.left_distrib, denote_insertSorted, Mon.mul_denote, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
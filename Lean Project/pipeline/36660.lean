import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Lemmas

open Bitraversable
variable {t : Type u → Type u → Type u} [Bitraversable t]
variable {β : Type u}
variable {β : Type u}
open Functor LawfulApplicative
variable {F G : Type u → Type u} [Applicative F] [Applicative G]
variable [LawfulBitraversable t] [LawfulApplicative F] [LawfulApplicative G]
open Bifunctor
open Function

example {α α' β} (f : α → α') (x : t α β) :
    tfst (F := Id) (pure ∘ f) x = pure (fst f x) := by
  rw [Bitraversable.tfst_eq_fst_id]
  apply bitraverse_eq_bimap_id

/- ACTUAL PROOF OF Bitraversable.tfst_eq_fst_id -/

example {α α' β} (f : α → α') (x : t α β) :
    tfst (F := Id) (pure ∘ f) x = pure (fst f x) := by
  apply bitraverse_eq_bimap_id
(** * LogRel.Syntax.BasicAst: definitions preceding those of the AST of terms: sorts, binder annotations… *)

Inductive sort : Set :=
  | set : sort.

Definition sort_of_product (s s' : sort) := set.

From Stdlib Require Logic.StrictProp.
From LogRel Require Import Utils.


Definition ell_list := list (prod nat bool).

Notation SFalse := Logic.StrictProp.sEmpty.
Notation STrue := Logic.StrictProp.sUnit.
#[projections(primitive)]Record SAnd (A B : SProp) : SProp := Sconj { Spr1 : A;  Spr2 : B }.
Arguments Spr1 {A B}.
Arguments Spr2 {A B}.


Fixpoint lt_ell n (ℓ : ell_list) : SProp :=
  match ℓ with
  | nil => STrue
  | cons (pair n' b') ℓ => SAnd (Logic.StrictProp.Squash (n < n')) (lt_ell n ℓ) 
  end.

Fixpoint ell_wf (ℓ : ell_list) : SProp :=
  match ℓ with
  | nil => STrue
  | cons (pair n b) ℓ => SAnd (lt_ell n ℓ) (ell_wf ℓ)
  end.


Definition Sis_true (b : bool) : SProp := if b then STrue else SFalse.


#[projections(primitive)]Record ell : Set := {
   ℓ_list :> ell_list;
   ℓ_wf : ell_wf ℓ_list;
   }.

Arguments eq_refl {_ _}, [_] _.
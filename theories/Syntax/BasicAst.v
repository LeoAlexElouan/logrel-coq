(** * LogRel.Syntax.BasicAst: definitions preceding those of the AST of terms: sorts, binder annotations… *)

Inductive sort : Set :=
  | set : sort.

Definition sort_of_product (s s' : sort) := set.

Definition ell_list := list (prod nat bool).

Fixpoint lt_ell n (ℓ : ell_list) : Prop :=
  match ℓ with
  | nil => True
  | cons (n', b') ℓ => n < n' /\ (lt_ell n ℓ) 
  end.

Fixpoint ell_wf (ℓ : ell_list) : Prop :=
  match ℓ with
  | nil => True
  | cons (n, b) ℓ => (lt_ell n ℓ) /\ ell_wf ℓ
  end.

Inductive SFalse : SProp := .
Inductive STrue : SProp := SI.
#[projections(primitive)]Record SAnd (A B : SProp) : SProp := Sconj { Spr1 : A;  Spr2 : B }.
Arguments Spr1 {A B}.
Arguments Spr2 {A B}.


Definition Sis_true (b : bool) : SProp := if b then STrue else SFalse.
From Stdlib Require Import Logic.StrictProp.

#[projections(primitive)]Record ell : Set := {
   ℓ_list :> ell_list;
   ℓ_wf : Squash (ell_wf ℓ_list);
   }.

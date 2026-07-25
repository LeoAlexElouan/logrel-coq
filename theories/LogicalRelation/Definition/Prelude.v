(** * LogRel.LogicalRelation.Definition.Prelude: Structures employed to define the logical relation *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Create HintDb logrel.
#[global] Hint Constants Opaque : logrel.
#[global] Hint Variables Transparent : logrel.
Ltac logrel := eauto with logrel.

(** Note: modules are used as a hackish solution to provide a form of namespaces for record projections. *)

(** ** Preliminaries *)

(** Instead of using induction-recursion, we encode simultaneously the fact that a type is reducible,
  and the graph of its decoding, as a single inductive relation.
  Concretely, the type of our reducibility relation is the following RedRel:
  for some R : RedRel, R Γ A B eqTm says
  that according to R, A is reducibly convertible to B in Γ and the associated reducible term equality
  is eqTm.
  One should think of RedRel as a functional relation taking three arguments (Γ, A and B) and returning
  eqTm as an output. *)

  Definition RedRel@{i j} :=
  context               ->
  decl                  ->
  decl                  ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(** An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation. *)

Module LRPack.

  Record LRPack@{i} {Γ : context} {A B : decl} :=
  {
    eqTm :  term -> term -> Type@{i};
  }.

  Arguments LRPack : clear implicits.

End LRPack.

Export LRPack(LRPack,Build_LRPack).

(* Notation "[ P | Γ ||- A ≅ B ]" := (@LRPack.eqTy Γ A P B). *)
Notation "[ P | Γ ||- t : A ]" := (@LRPack.eqTm Γ A A P t t).
Notation "[ P | Γ ||- t ≅ u : A ]" := (@LRPack.eqTm Γ A _ P t u).
Notation "[ P | Γ ||- t ≅ u : A ≅ B ]" := (@LRPack.eqTm Γ A B P t u).

(** An LRPack is adequate wrt. a RedRel when its unpacked eqTm component is. *)
Definition LRPackAdequate@{i j} {Γ : context}
  (R : RedRel@{i j}) {A B : term} (P : LRPack@{i} Γ A B) : Type@{j} :=
  R Γ A B P.(LRPack.eqTm).

Arguments LRPackAdequate _ _ _ /.

Module LRAd.

  Record > LRAdequate@{i j} {Γ : context} {R : RedRel@{i j}} {A B : term} : Type :=
  {
    pack :> LRPack@{i} Γ A B ;
    adequate :> LRPackAdequate@{i j} R pack
  }.

  Arguments LRAdequate : clear implicits.
  Arguments Build_LRAdequate {_ _ _ _ _}.

End LRAd.

Export LRAd(LRAdequate,Build_LRAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion LRAd.pack : LRAdequate >-> LRPack.
Coercion LRAd.adequate : LRAdequate >-> LRPackAdequate.

Notation "[ R | Γ ||- A ≅ B ]"              := (@LRAdequate Γ R A B).
Notation "[ R | Γ ||- t ≅ u : A | RA ]" := ((RA : LRPack Γ A _)(* .(@LRAd.pack Γ R A _) *).(LRPack.eqTm) t u).
Notation "[ R | Γ ||- t ≅ u : A ≅ B | RA ]" := ((RA : LRPack Γ A _)(* .(@LRAd.pack Γ R A B) *).(LRPack.eqTm) t u).

(** ** Uniform interface to access the wh normal form of type/term reducibility relations *)

Class WhRedTyRel `{ta : tag} `{WfType ta} `{RedType ta} `{ConvType ta} Γ (P : term -> term -> Type) := {
  whredtyL : forall {A B}, P A B -> [Γ |- A ↘ ] ;
  whredtyR : forall {A B}, P A B -> [Γ |- B ↘ ] ;
  whredty_conv : forall {A B} (h : P A B), [Γ |-[ta] (whredtyL h).(tyred_whnf) ≅ (whredtyR h).(tyred_whnf)] ;
}.

Class WhRedTm `{ta : tag} `{Typing ta} `{RedTerm ta} Γ A (P : term -> Type) := whredtm : forall {t}, P t -> [Γ |- t ↘ A ].
Class WhRedTmRel `{ta : tag} `{Typing ta} `{RedTerm ta} `{ConvTerm ta} Γ A (P : term -> term -> Type) := {
  whredtmL : forall {t u}, P t u -> [Γ |- t ↘ A ] ;
  whredtmR : forall {t u}, P t u -> [Γ |- u ↘ A ] ;
  whredtm_conv : forall {t u} (h : P t u), [Γ |- (whredtmL h).(tmred_whnf) ≅ (whredtmR h).(tmred_whnf) : A] ;
}.

(** Monad **)
Section Monad.
  Context `{GenericTypingProperties}.

Definition Rel_PSh
    (R : forall Γ A B, Type) Γ A B : PSh Γ:=
  fun Δ wfΔ (ρ : Δ ≤ Γ) => R Δ A⟨ρ⟩ B⟨ρ⟩.

Definition Split_Rel@{i} :
    (forall Γ A B, Type@{i}) -> (forall Γ A B, Type@{i}) :=
  fun R Γ A B => Split@{i} (fun Δ wfΔ (ρ : Δ ≤ Γ) => R Δ A⟨ρ⟩ B⟨ρ⟩).

Definition Rel_PSh_root (R : forall Γ (wfΓ : [|-Γ]) A B, Type) Γ wfΓ (A B : term) :
  (forall Δ wfΔ (ρ : Δ ≤ Γ), R Δ wfΔ A⟨ρ⟩ B⟨ρ⟩) -> R Γ wfΓ A B.
Proof. intros hPSh; specialize (hPSh Γ wfΓ wk_id); rewrite 2wk_id_ren_on in hPSh; tea. Qed.


Lemma wft_wk_inv : forall {Γ} {wfΓ : [|-Γ]} {A},(forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), [Δ |- A⟨ρ⟩]) -> [Γ |- A].
Proof.
  intros ??? hA.
  specialize (hA Γ wfΓ wk_id).
  now rewrite !wk_id_ren_on in hA.
Qed.

Lemma wft_shf {Γ A} : shf (fun Δ wfΔ (ρ : Δ ≤ Γ) => [Δ |- A⟨ρ⟩]).
Proof.
  intros ????? ht hf.
  eapply wft_split; tea.
Qed.

Lemma Split_bind_wft@{i} {Γ A} {C : PSh@{i} Γ} (hC : Split C) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> [Δ |- A⟨ρ⟩]) -> [Γ |- A].
Proof.
  intros hA.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply wft_wk_inv, (Split_bind_alg wft_shf hC hA).
Qed.

Lemma dSplit_bind_wft {Γ A} {C : PSh Γ} {P}
  {hC : Split C} (hP : dSplit P hC): 
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> overtree hP ρ -> [Δ |- A⟨ρ⟩])
  -> [Γ |- A ].
Proof.
  intros ht.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply wft_wk_inv, (dSplit_bind_alg wft_shf hP).
Qed.

Lemma convty_wk_inv : forall {Γ} {wfΓ : [|-Γ]} {A B},(forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]) -> [Γ |- A ≅ B].
Proof.
  intros ???? hAB.
  specialize (hAB Γ wfΓ wk_id).
  now rewrite 2!wk_id_ren_on in hAB.
Qed.

Lemma convty_shf {Γ A B} : shf (fun Δ wfΔ (ρ : Δ ≤ Γ) => [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]).
Proof.
  intros ???? ht hf.
  eapply convty_split; tea.
Qed.

Lemma Split_bind_convty {Γ A B} {C : PSh Γ} (hC : Split C) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]) -> [Γ |- A ≅ B].
Proof.
  intros hAB.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply convty_wk_inv, (Split_bind_alg convty_shf hC hAB).
Qed.

Lemma dSplit_bind_convty {Γ A B} {C : PSh Γ} {P}
  {hC : Split C} (hP : dSplit P hC): 
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> overtree hP ρ -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩])
  -> [Γ |- A ≅ B ].
Proof.
  intros ht.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply convty_wk_inv, (dSplit_bind_alg convty_shf hP).
Qed.

Lemma ty_wk_inv : forall {Γ} {wfΓ : [|-Γ]} {t A},
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), [Δ |- t⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t : A].
Proof.
  intros ???? ht.
  specialize (ht Γ wfΓ wk_id).
  rewrite wk_id_ren_on in ht.
  destruct A; tea.
  now rewrite <- wk_decl, wk_id_ren_on in ht.
Qed.

Lemma ty_shf {Γ t A} : shf (fun Δ wfΔ (ρ : Δ ≤ Γ) => [Δ |- t⟨ρ⟩ : A⟨ρ⟩]).
Proof.
  intros ???? ht hf.
  eapply ty_split; tea.
Qed.

Lemma Split_bind_ty {Γ t A} {C : PSh Γ} (hC : Split C) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t : A].
Proof.
  intros ht.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply ty_wk_inv, (Split_bind_alg ty_shf hC ht).
Qed.

Lemma dSplit_bind_ty {Γ t A} {C : PSh Γ} {P}
  {hC : Split C} (hP : dSplit P hC): 
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> overtree hP ρ -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩])
  -> [Γ |- t : A ].
Proof.
  intros ht.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply ty_wk_inv, (dSplit_bind_alg ty_shf hP).
Qed.

Lemma convtm_wk_inv : forall {Γ} {wfΓ : [|-Γ]} {t u A},
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t ≅ u : A].
Proof.
  intros ????? htu.
  specialize (htu Γ wfΓ wk_id).
  rewrite !wk_id_ren_on in htu.
  destruct A; tea.
  now rewrite <- wk_decl, wk_id_ren_on in htu.
Qed.

Lemma convtm_shf {Γ t u A} : shf (fun Δ wfΔ (ρ : Δ ≤ Γ) => [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]).
Proof.
  intros ???? ht hf.
  eapply convtm_split; tea.
Qed.

Lemma Split_bind_convtm {Γ t u A} {C : PSh Γ} (hC : Split C) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t ≅ u : A].
Proof.
  intros htu.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply convtm_wk_inv, (Split_bind_alg convtm_shf hC htu).
Qed.

Lemma dSplit_bind_convtm {Γ t u A} {C : PSh Γ} {P}
  {hC : Split C} (hP : dSplit P hC): 
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hC ρ -> overtree hP ρ -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩])
  -> [Γ |- t ≅ u : A ].
Proof.
  intros htu.
  assert ([|-Γ]) by apply hC.
  now unshelve eapply convtm_wk_inv, (dSplit_bind_alg convtm_shf hP).
Qed.

End Monad.


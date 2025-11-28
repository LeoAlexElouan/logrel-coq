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
  term                  ->
  term                  ->
  (term -> term -> Type@{i}) ->
  Type@{j}.

(** An LRPack contains the data corresponding to the codomain of RedRel seen as a functional relation. *)

Module LRPack.

  Record LRPack@{i} {Γ : context} {A B : term} :=
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
Notation "[ R | Γ ||- t ≅ u : A | RA ]" := (RA.(@LRAd.pack Γ R A _).(LRPack.eqTm) t u).
Notation "[ R | Γ ||- t ≅ u : A ≅ B | RA ]" := (RA.(@LRAd.pack Γ R A B).(LRPack.eqTm) t u).

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


Definition Rel_PSh (R : forall Γ A B, Type) Γ A B : PSh Γ :=
  fun Δ (ρ : Δ ≤ Γ) => R Δ A⟨ρ⟩ B⟨ρ⟩.

Definition Split_Rel@{i} : (forall Γ A B, Type@{i}) -> (forall Γ A B, Type@{i}) :=
  fun R Γ A B => Split@{i} (fun Δ (ρ : Δ ≤ Γ) => R Δ A⟨ρ⟩ B⟨ρ⟩).

Definition Rel_PSh_root (R : forall Γ A B, Type) Γ A B : (forall Δ (ρ : Δ ≤ Γ), R Δ A⟨ρ⟩ B⟨ρ⟩) -> R Γ A B.
Proof. intros hPSh; specialize (hPSh Γ wk_id); erewrite 2!wk_id_ren_on in hPSh; tea. Qed.


Notation Split_wfc A := (Split (fun Δ ρ => [|-Δ] -> A Δ ρ)).
Notation dSplit_wfc P hA := (dSplit (fun Δ ρ hA => forall (hΔ : [|-Δ]), P Δ ρ (hA hΔ)) hA).

Lemma wft_wk_inv `{GenericTypingProperties}: forall {Γ A}, [|-Γ] -> (forall Δ (ρ : Δ ≤ Γ),[|-Δ] ->  [Δ |- A⟨ρ⟩]) -> [Γ |- A].
Proof.
  intros ?? hΓ hA.
  specialize (hA Γ wk_id hΓ).
  now rewrite !wk_id_ren_on in hA.
Qed.

Lemma wft_shf `{GenericTypingProperties} {Γ A} : shf (fun Δ (ρ : Δ ≤ Γ) =>[|-Δ] -> [Δ |- A⟨ρ⟩]).
Proof.
  intros ??? ht hf hΔ.
  eapply wft_split; [eapply ht| eapply hf]; now eapply wfc_consF.
Qed.

Lemma Split_bind_wft `{GenericTypingProperties} {Γ A} {C : PSh Γ} (hΓ : [|-Γ]) (hC : Split C) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> [|-Δ] -> [Δ |- A⟨ρ⟩]) -> [Γ |- A].
Proof.
  intros h.
  eapply (wft_wk_inv hΓ).
  eapply (Split_bind_alg_over wft_shf hC h).
Qed.

Lemma convty_wk_inv `{GenericTypingProperties}: forall {Γ A B}, [|-Γ] -> (forall Δ (ρ : Δ ≤ Γ),[|-Δ] ->  [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]) -> [Γ |- A ≅ B].
Proof.
  intros ??? hΓ hAB.
  specialize (hAB Γ wk_id hΓ).
  now rewrite 2!wk_id_ren_on in hAB.
Qed.

Lemma convty_shf `{GenericTypingProperties} {Γ A B} : shf (fun Δ (ρ : Δ ≤ Γ) =>[|-Δ] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]).
Proof.
  intros ??? ht hf hΔ.
  eapply convty_split; [eapply ht| eapply hf]; now eapply wfc_consF.
Qed.

Lemma Split_bind_convty `{GenericTypingProperties} {Γ A B} {C : PSh Γ} (hΓ : [|-Γ]) (hC : Split C) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> [|-Δ] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩]) -> [Γ |- A ≅ B ].
Proof.
  intros h.
  eapply (convty_wk_inv hΓ).
  eapply (Split_bind_alg_over convty_shf hC h).
Qed.

Lemma ty_wk_inv `{GenericTypingProperties}: forall {Γ t A}, [|-Γ] -> (forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩ ]) -> [Γ |- t : A].
Proof.
  intros ??? hΓ ht.
  specialize (ht Γ wk_id hΓ).
  now rewrite 2!wk_id_ren_on in ht.
Qed.

Lemma ty_shf `{GenericTypingProperties} {Γ t A} : shf (fun Δ (ρ : Δ ≤ Γ) => [|-Δ] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩]).
Proof.
  intros ??? ht hf hΔ.
  eapply ty_split; [eapply ht| eapply hf]; now eapply wfc_consF.
Qed.

Lemma Split_bind_ty `{GenericTypingProperties} {Γ t A} {C : PSh Γ} (hΓ : [|-Γ]) (hC : Split C) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> [|-Δ] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t : A ].
Proof.
  intros h.
  eapply (ty_wk_inv hΓ).
  eapply (Split_bind_alg_over ty_shf hC h).
Qed.

Lemma dSplit_bind_ty `{GenericTypingProperties} {Γ t A} {C : PSh Γ} {P} (hΓ : [|-Γ])
  {hC : Split C} (hP : dSplit P hC):
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> overtree hP.(dtree) Δ-> [|-Δ] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t : A ].
Proof.
  intros h.
  eapply (ty_wk_inv hΓ).
  now eapply (dSplit_bind_alg_over ty_shf hP).
Qed.

Lemma convtm_wk_inv `{GenericTypingProperties}: forall {Γ t u A}, [|-Γ] -> (forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ ]) -> [Γ |- t ≅ u : A].
Proof.
  intros ???? hΓ htu.
  specialize (htu Γ wk_id hΓ).
  now rewrite 3!wk_id_ren_on in htu.
Qed.

Lemma convtm_shf `{GenericTypingProperties} {Γ t u A} : shf (fun Δ (ρ : Δ ≤ Γ) => [|-Δ] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]).
Proof.
  intros ??? ht hf hΔ.
  eapply convtm_split; [eapply ht| eapply hf]; now eapply wfc_consF.
Qed.

Lemma Split_bind_convtm `{GenericTypingProperties} {Γ t u A} {C : PSh Γ} (hΓ : [|-Γ]) (hC : Split C) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> [|-Δ] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t ≅ u : A ].
Proof.
  intros h.
  eapply (convtm_wk_inv hΓ).
  eapply (Split_bind_alg_over convtm_shf hC h).
Qed.

Lemma dSplit_bind_convtm `{GenericTypingProperties} {Γ t u A} {C : PSh Γ} {P} (hΓ : [|-Γ])
  {hC : Split C} (hP : dSplit P hC):
  (forall Δ (ρ : Δ ≤ Γ), overtree hC.(dtree) Δ -> overtree hP.(dtree) Δ-> [|-Δ] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩]) -> [Γ |- t ≅ u : A ].
Proof.
  intros h.
  eapply (convtm_wk_inv hΓ).
  eapply (dSplit_bind_alg_over convtm_shf hP h).
Qed.



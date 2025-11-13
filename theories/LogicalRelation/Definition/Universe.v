(** * LogRel.LogicalRelation.Definition.Universe : Definition of the logical relation for universes *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Prelude.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Universe levels *)

Inductive TypeLevel : Set :=
  | zero : TypeLevel
  | one  : TypeLevel.

Inductive TypeLevelLt : TypeLevel -> TypeLevel -> Set :=
  | Oi : TypeLevelLt zero one.

Notation "A << B" := (TypeLevelLt A B).

Definition LtSubst {l} (h : l = one) : zero << l.
Proof.
  rewrite h.
  constructor.
Qed.

Definition elim {l : TypeLevel} (h : l << zero) : False :=
  match h in _ << lz return (match lz with | zero => False | one => True end) with
    | Oi => I
  end.

Definition ltInd (P : TypeLevel -> Type) (ih : (forall l, (forall l', l' << l -> P l') -> P l))
  : forall l, P l.
Proof.
  assert (P zero) by (apply ih; intros ? []%elim).
  intros []; tea; apply ih; intros ? h; now inversion h.
Qed.

(** ** Reducibility of the universe *)

Module URedTy.

  Record SURedTy `{ta : tag} `{!WfType ta} `{!RedType ta} {l} {Γ : context} {A B : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    redL : [ Γ |- A  :⤳*: U ] ;
    redR : [ Γ |- B  :⤳*: U ] ;
  }.

  Arguments SURedTy {_ _ _}.

  Definition wfCtx  `{WfContextProperties}  {l} {Γ : context} {A B : term} : SURedTy l Γ A B -> [|- Γ].
  Proof. intros []; timeout 1 gen_typing. Qed.

  Definition whredL `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    SURedTy l Γ A B -> [Γ |- A ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

  Definition whredR `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    SURedTy l Γ A B -> [Γ |- B ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

  Definition URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} l (Γ : context) (A B : term) :
    Set :=
    Split (fun Δ (ρ : Δ ≤ Γ) => SURedTy l Δ A⟨ρ⟩ B⟨ρ⟩).

End URedTy.

Export URedTy(URedTy, SURedTy, Build_SURedTy).

#[program]
Instance URedTyWhRedTy `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (SURedTy l Γ) :=
 {| whredtyL := fun A B RAB => URedTy.whredL RAB ;
    whredtyR := fun A B RAB => URedTy.whredR RAB ;
 |}.
Next Obligation. destruct h; gtyping. Qed.

Notation "[ Γ ||-SU< l > A ≅ B ]" := (SURedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).
Notation "[ Γ ||-U< l > A ≅ B ]" := (URedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).

Import EqNotations.

Lemma level_unique `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
  {Γ lA lB l A A' B B'}
  (RA : [Γ ||-SU<lA> A ≅ A'])
  (RB : [Γ ||-SU<lB> B ≅ B'])
  (RAB : [Γ ||-SU<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
Proof.
  (* If we introduce more universes this lemma should still hold because
    RAB entails that A ⤳* U RAB.(level), B ⤳* U RAB.(level)
    also A ⤳* RA.(level) and B ⤳* RB.(level) and by determinism of reduction
    RA.(level) = RAB.(level) = RB.(level)
  *)
  destruct RA as [? []], RB as [? []]; reflexivity.
Qed.

Lemma level_unique' `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
  {Γ lA lB l A A' B B'}
  (RA : [Γ ||-SU<lA> A' ≅ A])
  (RB : [Γ ||-SU<lB> B' ≅ B])
  (RAB : [Γ ||-SU<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
Proof.
  (* If we introduce more universes this lemma should still hold because
    RAB entails that A ⤳* U RAB.(level), B ⤳* U RAB.(level)
    also A ⤳* RA.(level) and B ⤳* RB.(level) and by determinism of reduction
    RA.(level) = RAB.(level) = RB.(level)
  *)
  destruct RA as [? []], RB as [? []]; reflexivity.
Qed.

Module URedTm.

  Record SURedTm `{ta : tag} `{Typing ta} `{RedTerm ta}
    {level : TypeLevel} {Γ : context} {t : term}
  : Set := {
    te : term;
    red : [ Γ |- t :⤳*: te : U (* level *) ];
    type : isType te;
  }.

  Arguments SURedTm {_ _ _}.

  Definition URedTm `{ta : tag} `{Typing ta} `{RedTerm ta} `{WfContext ta}
    (level : TypeLevel) (Γ : context) (t : term) :
      Set :=
      Split (fun Δ (ρ : Δ ≤ Γ) => [|-Δ] -> SURedTm level Δ t⟨ρ⟩).

  Definition whred `{ta : tag} `{Typing ta} `{RedTerm ta}
    {l} {Γ : context} {t: term} :
    SURedTm l Γ t -> [Γ |- t ↘  U].
  Proof. intros []; gtyping. Defined.

  Record SURedTmEq@{i j} `{ta : tag} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {A B : term} {R : [Γ ||-SU<l> A ≅ B]} {t u}
  : Type@{j} := {
      redL : SURedTm R.(URedTy.level) Γ t ;
      redR : SURedTm R.(URedTy.level) Γ u ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ];
      relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u ] ;
  }.

  Arguments SURedTmEq {_ _ _ _ _ _ _ } rec.

  Definition URedTmEq@{i j} `{ta : tag} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta} `{WfContext ta}
    {l} (rec : forall l', l' << l -> RedRel@{i j}) (Γ : context) (A B : term) (R :forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]) t u:
      Type@{j} :=
      Split (fun Δ (ρ : Δ ≤ Γ) => forall (hΔ : [|-Δ]), SURedTmEq rec Δ A⟨ρ⟩ B⟨ρ⟩ (R Δ ρ hΔ) t⟨ρ⟩ u⟨ρ⟩).

  Definition whredL `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-SU<l> A ≅ B]} :
    SURedTmEq rec Γ A B R t u -> [Γ |- t ↘  U].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-SU<l> A ≅ B]} :
    SURedTmEq rec Γ A B R t u -> [Γ |- u ↘  U].
  Proof. intros []; now eapply whred. Defined.


End URedTm.

Export URedTm(URedTm, SURedTm, Build_SURedTm,URedTmEq, SURedTmEq, Build_SURedTmEq).
Notation "[ rec | Γ ||-SU t ≅ u : A | R ]" := (SURedTmEq rec Γ A _ R t u) (at level 0, R, Γ, t, u, A, rec at level 50).
Notation "[ rec | Γ ||-SU t ≅ u : A ≅ B | R ]" := (URedTmEq rec Γ A B R t u) (at level 0, R, Γ, t, u, A, B, rec at level 50).
Notation "[ rec | Γ ||-U t ≅ u : A | R ]" := (URedTmEq rec Γ A _ R t u) (at level 0, R, Γ, t, u, A, rec at level 50).
Notation "[ rec | Γ ||-U t ≅ u : A ≅ B | R ]" := (URedTmEq rec Γ A B R t u) (at level 0, R, Γ, t, u, A, B, rec at level 50).

Instance URedTmWhRed `{GenericTypingProperties} {Γ l} : WhRedTm Γ U (SURedTm l Γ) :=
  fun t => URedTm.whred.


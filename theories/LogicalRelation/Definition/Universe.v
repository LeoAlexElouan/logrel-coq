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

  Record URedTy `{ta : tag} `{!WfType ta} `{!RedType ta} {l} {Γ : context} {A B : term}
  : Set := {
    level  : TypeLevel;
    lt  : level << l;
    redL : [ Γ |- A  :⤳*: U ] ;
    redR : [ Γ |- B  :⤳*: U ] ;
  }.

  Arguments URedTy {_ _ _}.

  Definition wfCtx  `{WfContextProperties}  {l} {Γ : context} {A B : term} : URedTy l Γ A B -> [|- Γ].
  Proof. intros []; timeout 1 gen_typing. Qed.

  Definition whredL `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    URedTy l Γ A B -> [Γ |- A ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

  Definition whredR `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta} {l} {Γ : context} {A B : term} :
    URedTy l Γ A B -> [Γ |- B ↘ ].
  Proof. intros []; timeout 1 gen_typing. Defined.

  Definition shfURedTy `{ta : tag} `{!WfType ta} `{!RedType ta} l (Γ : context) (A B : term) :
    Set :=
    Split (fun Δ (ρ : Δ ≤ Γ) => URedTy l Δ A⟨ρ⟩ B⟨ρ⟩).

End URedTy.

Export URedTy(shfURedTy, URedTy, Build_URedTy).

#[program]
Instance URedTyWhRedTy `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (URedTy l Γ) :=
 {| whredtyL := fun A B RAB => URedTy.whredL RAB ;
    whredtyR := fun A B RAB => URedTy.whredR RAB ;
 |}.
Next Obligation. destruct h; gtyping. Qed.

Notation "[ Γ ||-U< l > A ≅ B ]" := (URedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).
Notation "[ Γ ||-shfU< l > A ≅ B ]" := (shfURedTy l Γ A B) (at level 0, Γ, l, A, B at level 50).

Import EqNotations.

Lemma level_unique `{ta : tag} `{!WfType ta} `{!RedType ta} `{WfContext ta}
  {Γ lA lB l A A' B B'}
  (RA : [Γ ||-U<lA> A ≅ A'])
  (RB : [Γ ||-U<lB> B ≅ B'])
  (RAB : [Γ ||-U<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
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
  (RA : [Γ ||-U<lA> A' ≅ A])
  (RB : [Γ ||-U<lB> B' ≅ B])
  (RAB : [Γ ||-U<l> A ≅ B]) : RA.(URedTy.level) = RB.(URedTy.level).
Proof.
  (* If we introduce more universes this lemma should still hold because
    RAB entails that A ⤳* U RAB.(level), B ⤳* U RAB.(level)
    also A ⤳* RA.(level) and B ⤳* RB.(level) and by determinism of reduction
    RA.(level) = RAB.(level) = RB.(level)
  *)
  destruct RA as [? []], RB as [? []]; reflexivity.
Qed.

Module URedTm.

  Record URedTm `{ta : tag} `{Typing ta} `{RedTerm ta}
    {level : TypeLevel} {Γ : context} {t : term}
  : Set := {
    te : term;
    red : [ Γ |- t :⤳*: te : U (* level *) ];
    type : isType te;
  }.

  Arguments URedTm {_ _ _}.

  Definition shfURedTm `{ta : tag} `{Typing ta} `{RedTerm ta} `{WfContext ta}
    (level : TypeLevel) (Γ : context) (t : term) :
      Set :=
      Split (fun Δ (ρ : Δ ≤ Γ) => [|-Δ] -> URedTm level Δ t⟨ρ⟩).

  Definition whred `{ta : tag} `{Typing ta} `{RedTerm ta}
    {l} {Γ : context} {t: term} :
    URedTm l Γ t -> [Γ |- t ↘  U].
  Proof. intros []; gtyping. Defined.

  Record URedTmEq@{i j} `{ta : tag} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall {l'}, l' << l -> RedRel@{i j}}
    {Γ : context} {A B : term} {R : [Γ ||-U<l> A ≅ B]} {t u}
  : Type@{j} := {
      redL : URedTm R.(URedTy.level) Γ t ;
      redR : URedTm R.(URedTy.level) Γ u ;
      eq   : [ Γ |- redL.(te) ≅ redR.(te) : U ];
      relEq : [ rec R.(URedTy.lt) | Γ ||- t ≅ u ] ;
  }.

  Arguments URedTmEq {_ _ _ _ _ _ _ } rec.

  Definition shfURedTmEq@{i j} `{ta : tag} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta} `{WfContext ta}
    {l} (rec : forall l', l' << l -> RedRel@{i j}) (Γ : context) (A B : term) (R :forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-U<l> A⟨ρ⟩ ≅ B⟨ρ⟩]) t u:
      Type@{j} :=
      Split (fun Δ (ρ : Δ ≤ Γ) => forall (hΔ : [|-Δ]), URedTmEq rec Δ A⟨ρ⟩ B⟨ρ⟩ (R Δ ρ hΔ) t⟨ρ⟩ u⟨ρ⟩).

  Definition whredL `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ A B R t u -> [Γ |- t ↘  U].
  Proof. intros []; now eapply whred. Defined.

  Definition whredR `{ta : tag} `{WfContext ta} `{WfType ta}
    `{Typing ta} `{ConvTerm ta} `{RedType ta} `{RedTerm ta}
    {l} {rec : forall l', l' << l -> RedRel}
    {Γ : context} {t u A B : term} {R : [Γ ||-U<l> A ≅ B]} :
    URedTmEq rec Γ A B R t u -> [Γ |- u ↘  U].
  Proof. intros []; now eapply whred. Defined.


End URedTm.

Export URedTm(URedTm, shfURedTm, Build_URedTm,URedTmEq, shfURedTmEq, Build_URedTmEq).
Notation "[ rec | Γ ||-shfU t ≅ u : A | R ]" := (shfURedTmEq rec Γ A _ R t u) (at level 0, R, Γ, t, u, A, rec at level 50).
Notation "[ rec | Γ ||-shfU t ≅ u : A ≅ B | R ]" := (shfURedTmEq rec Γ A B R t u) (at level 0, R, Γ, t, u, A, B, rec at level 50).
Notation "[ rec | Γ ||-U t ≅ u : A | R ]" := (URedTmEq rec Γ A _ R t u) (at level 0, R, Γ, t, u, A, rec at level 50).
Notation "[ rec | Γ ||-U t ≅ u : A ≅ B | R ]" := (URedTmEq rec Γ A B R t u) (at level 0, R, Γ, t, u, A, B, rec at level 50).

Instance URedTmWhRed `{GenericTypingProperties} {Γ l} : WhRedTm Γ U (URedTm l Γ) :=
  fun t => URedTm.whred.


(** * LogRel.LogicalRelation.Definition.Bool : Definition of the logical relation for bool *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of boolean type *)
Module BoolRedTy.

  Record SBoolRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tBool] ;
    redR : [Γ |- B :⤳*: tBool]
  }.

  Arguments SBoolRedTy {_ _ _}.

  Definition BoolRedTy `{ta : tag} `{WfType ta} `{RedType ta} : forall Γ A B, Type :=
    Split_Rel SBoolRedTy.

  Section BoolRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : SBoolRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : SBoolRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End BoolRedTy.

End BoolRedTy.

Export BoolRedTy(SBoolRedTy, BoolRedTy, Build_SBoolRedTy).
Notation "[ Γ ||-SBool A ≅ B ]" := (BoolRedTy Γ A B) (at level 0, Γ, A at level 50).
Notation "[ Γ ||-Bool A ≅ B ]" := (BoolRedTy Γ A B) (at level 0, Γ, A at level 50).

#[program]
Instance WhRedTyBoolRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (SBoolRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => BoolRedTy.whredL RAB ;
    whredtyR := fun A B RAB => BoolRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.


Module BoolRedTmEq.
Section BoolRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive BoolPropEq Γ : term -> term -> Set :=
  | trueReq :
    BoolPropEq Γ tTrue tTrue
  | falseReq :
    BoolPropEq Γ tFalse tFalse
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tBool] -> BoolPropEq Γ ne ne'.


  Record SBoolRedTmEq {Γ t u} : Set :=
    {
      nfL : term ;
      nfR : term ;
      redL : [Γ |- t :⤳*: nfL : tBool] ;
      redR : [Γ |- u :⤳*: nfR : tBool ] ;
      eq : [Γ |- nfL ≅ nfR : tBool] ;
      prop : BoolPropEq Γ nfL nfR
  }.
  Arguments SBoolRedTmEq : clear implicits.

  Definition BoolRedTmEq : forall Γ t u, Set :=
    Split_Rel SBoolRedTmEq.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Lemma BoolPropEq_isBool Γ {t t' : term} :
      BoolPropEq Γ t t' -> isBool t × isBool t'.
    Proof.
      intros [| |?? []]; split; constructor.
      all: eapply convneu_whne; eassumption + now symmetry.
    Defined.

    Definition whnfL {Γ t u} : BoolPropEq Γ t u -> whnf t.
    Proof. intros []%BoolPropEq_isBool; now eapply isBool_whnf. Qed.

    Definition whnfR {Γ t u} : BoolPropEq Γ t u -> whnf u.
    Proof. intros []%BoolPropEq_isBool; now eapply isBool_whnf. Qed.

    Definition whredL {Γ t u} : SBoolRedTmEq Γ t u -> [Γ |- t ↘ tBool].
    Proof.
      intros []; econstructor; tea; now eapply whnfL.
    Defined.

    Definition whredR {Γ t u} : SBoolRedTmEq Γ t u -> [Γ |- u ↘ tBool].
    Proof.
      intros []; econstructor; tea; now eapply whnfR.
    Defined.

  End Def.


End BoolRedTmEq.
Arguments BoolPropEq {_ _ _}.
Arguments SBoolRedTmEq {_ _ _ _ _}.
Arguments BoolRedTmEq {_ _ _ _ _}.
End BoolRedTmEq.

Export BoolRedTmEq(BoolRedTmEq,SBoolRedTmEq,Build_SBoolRedTmEq,BoolPropEq,BoolPropEq_isBool).

Notation "[ Γ ||-SBool t ≅ u :Bool]" := (@SBoolRedTmEq _ _ _ _ _ _ _ Γ t u).
Notation "[ Γ ||-Bool t ≅ u :Bool]" := (@BoolRedTmEq _ _ _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u at level 50). *)

#[program]
Instance BoolRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tBool (SBoolRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => BoolRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => BoolRedTmEq.whredR Rtu |}.
Next Obligation.
  now destruct h.
Qed.
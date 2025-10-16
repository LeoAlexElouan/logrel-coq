(** * LogRel.LogicalRelation.Definition.Bool : Definition of the logical relation for bool *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of boolean type *)
Module BoolRedTy.

  Record BoolRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tBool] ;
    redR : [Γ |- B :⤳*: tBool]
  }.

  Arguments BoolRedTy {_ _ _}.

  Section BoolRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : BoolRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : BoolRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End BoolRedTy.

End BoolRedTy.

Export BoolRedTy(BoolRedTy, Build_BoolRedTy).
Notation "[ Γ ||-Bool A ≅ B ]" := (BoolRedTy Γ A B) (at level 0, Γ, A at level 50).

#[program]
Instance WhRedTyBoolRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (BoolRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => BoolRedTy.whredL RAB ;
    whredtyR := fun A B RAB => BoolRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.


Module BoolRedTmEq.
Section BoolRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context}.

  Inductive BoolPropEq : term -> term -> Set :=
  | trueReq :
    BoolPropEq tTrue tTrue
  | falseReq :
    BoolPropEq tFalse tFalse
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tBool] -> BoolPropEq ne ne'.


  Record BoolRedTmEq {t u} : Set :=
    {
      nfL : term ;
      nfR : term ;
      redL : [Γ |- t :⤳*: nfL : tBool] ;
      redR : [Γ |- u :⤳*: nfR : tBool ] ;
      eq : [Γ |- nfL ≅ nfR : tBool] ;
      prop : BoolPropEq nfL nfR
  }.
  Arguments BoolRedTmEq : clear implicits.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Lemma BoolPropEq_isBool {t t' : term} :
      BoolPropEq t t' -> isBool t × isBool t'.
    Proof.
      intros [| |?? []]; split; constructor.
      all: eapply convneu_whne; eassumption + now symmetry.
    Defined.

    Definition whnfL {t u} : BoolPropEq t u -> whnf t.
    Proof. intros []%BoolPropEq_isBool; now eapply isBool_whnf. Qed.

    Definition whnfR {t u} : BoolPropEq t u -> whnf u.
    Proof. intros []%BoolPropEq_isBool; now eapply isBool_whnf. Qed.

    Definition whredL {t u} : BoolRedTmEq t u -> [Γ |- t ↘ tBool].
    Proof.
      intros []; econstructor; tea; now eapply whnfL.
    Defined.

    Definition whredR {t u} : BoolRedTmEq t u -> [Γ |- u ↘ tBool].
    Proof.
      intros []; econstructor; tea; now eapply whnfR.
    Defined.

  End Def.


End BoolRedTmEq.
Arguments BoolPropEq {_ _ _}.
Arguments BoolRedTmEq {_ _ _ _ _}.
End BoolRedTmEq.

Export BoolRedTmEq(BoolRedTmEq,Build_BoolRedTmEq,BoolPropEq,BoolPropEq_isBool).

Notation "[ Γ ||-Bool t ≅ u :Bool]" := (@BoolRedTmEq _ _ _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u at level 50). *)

#[program]
Instance BoolRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tBool (BoolRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => BoolRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => BoolRedTmEq.whredR Rtu |}.
Next Obligation.
  now destruct h.
Qed.
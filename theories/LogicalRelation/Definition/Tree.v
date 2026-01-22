(** * LogRel.LogicalRelation.Definition.Tree : Definition of the logical relation for tree *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne Nat.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of natural number type *)
Module TreeRedTy.

  Record TreeRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tTree] ;
    redR : [Γ |- B :⤳*: tTree]
  }.

  Arguments TreeRedTy {_ _ _}.

  Section TreeRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : TreeRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : TreeRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End TreeRedTy.

End TreeRedTy.

Export TreeRedTy(TreeRedTy, Build_TreeRedTy).
Notation "[ Γ ||-Tree A ≅ B ]" := (TreeRedTy Γ A B) (at level 0, Γ, A at level 50).


#[program]
Instance WhRedTyTreeRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (TreeRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => TreeRedTy.whredL RAB ;
    whredtyR := fun A B RAB => TreeRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.

Module TreeRedTmEq.
Section TreeRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {Γ : context}.

  Variant treeTmEqVariant : Set := RedEq | PropEq.

  Inductive TreeTmEq : treeTmEqVariant -> term -> term -> Set :=
  | Build_TreeRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⤳*: nfL : tTree])
    (redR : [Γ |- u :⤳*: nfR : tTree ])
    (eq : [Γ |- nfL ≅ nfR : tTree])
    (prop : TreeTmEq PropEq nfL nfR) : TreeTmEq RedEq t u
  | leafReq {n n'}
    (Rn : NatRedTmEq Γ n n') :
    TreeTmEq PropEq (tLeaf n) (tLeaf n')
  | nodeReq {n n' tl tl' tr tr'}
    (Rn : NatRedTmEq Γ n n')
    (Rtl : TreeTmEq RedEq tl tl')
    (Rtr : TreeTmEq RedEq tr tr') :
    TreeTmEq PropEq (tNode n tl tr) (tNode n' tl' tr')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tTree] -> TreeTmEq PropEq ne ne'.

  Definition TreePropEq := (TreeTmEq PropEq).
  Definition TreeRedTmEq := (TreeTmEq RedEq).

  Definition TreeRedTmEq_destruct : forall (P : forall t u, TreeRedTmEq t u -> Type),
    (forall t u nfL nfR redL redR eq prop, P t u (Build_TreeRedTmEq nfL nfR redL redR eq prop)) ->
    forall t u (Rtu : TreeRedTmEq t u), P t u Rtu := fun P hBuild t u Rtu =>
      match Rtu as Rtu' in TreeTmEq v t' u'
        return (match v with
          | RedEq => fun (R : TreeTmEq RedEq t' u') => P t' u' R
          | _ => fun _ => unit end Rtu') with
      | @Build_TreeRedTmEq t u nfL nfR redL redR eq prop => hBuild t u nfL nfR redL redR eq prop
      | _ => tt end.

  Definition TreePropEq_destruct : forall (P : forall t u, TreePropEq t u -> Type),
    (forall n n' Rn, P (tLeaf n) (tLeaf n') (@leafReq n n' Rn)) ->
    (forall n n' tl tl' tr tr' Rn Rtl Rtr, P (tNode n tl tr) (tNode n' tl' tr') (@nodeReq n n' tl tl' tr tr' Rn Rtl Rtr)) ->
    (forall ne ne' Rne, P ne ne' (@neReq ne ne' Rne)) ->
    forall t u (Rtu : TreePropEq t u), P t u Rtu := fun P hl hn hne t u Rtu =>
      match Rtu as Rtu' in TreeTmEq v t' u'
        return (match v with
          | PropEq => fun (R : TreeTmEq PropEq t' u') => P t' u' R
          | _ => fun _ => (unit : Type) end Rtu') with
      | leafReq Rn => hl _ _ Rn
      | nodeReq Rn Rtl Rtr => hn _ _ _ _ _ _ Rn Rtl Rtr
      | neReq Rne => hne _ _ Rne
      | _ => tt end.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Lemma TreePropEq_isTree {t t' : term} :
      TreePropEq t t' -> isTree t × isTree t'.
    Proof.
      intros Rt. induction Rt  as [ | |?? []] using TreePropEq_destruct; split; constructor.
      all: eapply convneu_whne; eassumption + now symmetry.
    Defined.

    Definition whnfL {t u} : TreePropEq t u -> whnf t.
    Proof. intros []%TreePropEq_isTree; now eapply isTree_whnf. Qed.

    Definition whnfR {t u} : TreePropEq t u -> whnf u.
    Proof. intros []%TreePropEq_isTree; now eapply isTree_whnf. Qed.

    Definition whredL {t u} : TreeRedTmEq t u -> [Γ |- t ↘ tTree].
    Proof.
      intros Rt.
      induction Rt as [] using TreeRedTmEq_destruct; econstructor; tea; now eapply whnfL.
    Defined.

    Definition whredR {t u} : TreeRedTmEq t u -> [Γ |- u ↘ tTree].
    Proof.
      intros Rt.
      destruct Rt as [] using TreeRedTmEq_destruct; econstructor; tea; now eapply whnfR.
    Defined.

  End Def.



End TreeRedTmEq.

Arguments TreeRedTmEq {_ _ _ _ _}.
Arguments TreeTmEq {_ _ _ _ _}.
End TreeRedTmEq.

Export TreeRedTmEq(TreeRedTmEq,Build_TreeRedTmEq, TreePropEq, TreePropEq_isTree).


Notation "[ Γ ||-Tree t ≅ u :Tree]" := (@TreeRedTmEq _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u, A, RA at level 50). *)

#[program]
Instance TreeRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tTree (TreeRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => TreeRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => TreeRedTmEq.whredR Rtu |}.
Next Obligation.
  now induction t, u, h using TreeRedTmEq.TreeRedTmEq_destruct.
Qed.



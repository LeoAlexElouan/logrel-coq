(** * LogRel.LogicalRelation.Definition.Nat : Definition of the logical relation for nat *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Prelude Ne.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


(** ** Reducibility of natural number type *)
Module NatRedTy.

  Record SNatRedTy `{ta : tag} `{WfType ta} `{RedType ta}
    {Γ : context} {A B : term}
  : Set :=
  {
    redL : [Γ |- A :⤳*: tNat] ;
    redR : [Γ |- B :⤳*: tNat]
  }.

  Arguments SNatRedTy {_ _ _}.

  Definition NatRedTy `{ta : tag} `{WfType ta} `{RedType ta} Γ A B : Type :=
    Split (fun Δ (ρ : Δ ≤ Γ) => SNatRedTy Δ A⟨ρ⟩  B⟨ρ⟩).

  Section NatRedTy.
  Context `{ta : tag} `{WfType ta} `{RedType ta}.

  Definition whredL {Γ A B} : SNatRedTy Γ A B -> [Γ |- A ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  Definition whredR {Γ A B} : SNatRedTy Γ A B -> [Γ |- B ↘].
  Proof. intros []; econstructor; tea; constructor. Defined.

  End NatRedTy.

End NatRedTy.

Export NatRedTy(SNatRedTy, Build_SNatRedTy, NatRedTy).
Notation "[ Γ ||-SNat A ≅ B ]" := (SNatRedTy Γ A B) (at level 0, Γ, A at level 50).
Notation "[ Γ ||-Nat A ≅ B ]" := (NatRedTy Γ A B) (at level 0, Γ, A at level 50).


#[program]
Instance WhRedTyNatRedTy `{GenericTypingProperties} {Γ} : WhRedTyRel Γ (SNatRedTy Γ) :=
  {|
    whredtyL := fun A B RAB => NatRedTy.whredL RAB ;
    whredtyR := fun A B RAB => NatRedTy.whredR RAB ;
  |}.
Next Obligation. destruct h; gtyping. Qed.


Module NatRedTmEq.
Section NatRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Inductive SNatRedTmEq (Γ : context) : term -> term -> Set :=
  | Build_SNatRedTmEq {t u}
    (nfL nfR : term)
    (redL : [Γ |- t :⤳*: nfL : tNat])
    (redR : [Γ |- u :⤳*: nfR : tNat ])
    (eq : [Γ |- nfL ≅ nfR : tNat])
    (prop : NatPropEq Γ nfL nfR) : SNatRedTmEq Γ t u

  with NatPropEq (Γ : context): term -> term -> Set :=
  | zeroReq :
    NatPropEq Γ tZero tZero
  | succReq {n n'} :
    NatRedTmEq Γ n n' ->
    NatPropEq Γ(tSucc n) (tSucc n')
  | neReq {ne ne'} : [Γ ||-NeNf ne ≅ ne' : tNat] -> NatPropEq Γ ne ne'

  with NatRedTmEq (Γ : context) : term -> term -> Set :=
  | Build_NatRedTmEq t u (d : DTree Γ): (forall Δ (ρ : Δ ≤ Γ), overtree d Δ -> SNatRedTmEq Δ t⟨ρ⟩ u⟨ρ⟩) -> NatRedTmEq Γ t u.

  Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Lemma NatPropEq_isNat Γ {t t' : term} :
      NatPropEq Γ t t' -> isNat t × isNat t'.
    Proof.
      intros [| |?? []]; split; constructor.
      all: eapply convneu_whne; eassumption + now symmetry.
    Defined.

    Definition whnfL {Γ t u} : NatPropEq Γ t u -> whnf t.
    Proof. intros []%NatPropEq_isNat; now eapply isNat_whnf. Qed.

    Definition whnfR {Γ t u} : NatPropEq Γ t u -> whnf u.
    Proof. intros []%NatPropEq_isNat; now eapply isNat_whnf. Qed.

    Definition whredL {Γ t u} : SNatRedTmEq Γ t u -> [Γ |- t ↘ tNat].
    Proof.
      intros []; econstructor; tea; now eapply whnfL.
    Defined.

    Definition whredR {Γ t u} : SNatRedTmEq Γ t u -> [Γ |- u ↘ tNat].
    Proof.
      intros []; econstructor; tea; now eapply whnfR.
    Defined.

  End Def.


Scheme SNatRedTmEq_mut_rect := Induction for SNatRedTmEq Sort Type with
    NatPropEq_mut_rect := Induction for NatPropEq Sort Type with
    NatRedTmEq_mut_rect := Induction for NatRedTmEq Sort Type.

Combined Scheme _NatRedInduction from
  SNatRedTmEq_mut_rect,
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Combined Scheme _NatRedEqInduction from
  SNatRedTmEq_mut_rect,
  NatRedTmEq_mut_rect,
  NatPropEq_mut_rect.

Let _NatRedEqInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _NatRedEqInduction);
      let ind_ty := type of ind in
      exact ind_ty).

Let NatRedEqInductionType :=
  ltac: (let ind := eval cbv delta [_NatRedEqInductionType] zeta
    in _NatRedEqInductionType in
    let ind' := polymorphise ind in
  exact ind').

(* KM: looks like there is a bunch of polymorphic universes appearing there... *)
Lemma NatRedEqInduction : NatRedEqInductionType.
Proof.
  intros PSRedEq PPropEq PRedEq **; split; [|split]; now apply (_NatRedEqInduction PSRedEq PPropEq PRedEq).
Defined.

End NatRedTmEq.
Arguments SNatRedTmEq {_ _ _ _ _}.
Arguments NatPropEq {_ _ _ _ _}.
Arguments NatRedTmEq {_ _ _ _ _}.
End NatRedTmEq.

Export NatRedTmEq(NatRedTmEq,Build_NatRedTmEq,SNatRedTmEq,Build_SNatRedTmEq, NatPropEq, NatRedEqInduction, NatPropEq_isNat).

Notation "[ Γ ||-SNat t ≅ u :Nat]" := (@SNatRedTmEq _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u, A, RA at level 50). *)
Notation "[ Γ ||-Nat t ≅ u :Nat]" := (@NatRedTmEq _ _ _ _ _ Γ t u).  (* (at level 0, Γ, t, u, A, RA at level 50). *)

#[program]
Instance NatRedTmEqWhRed `{GenericTypingProperties} {Γ} : WhRedTmRel Γ tNat (SNatRedTmEq Γ) :=
  {| whredtmL := fun t u Rtu => NatRedTmEq.whredL Rtu ;
    whredtmR := fun t u Rtu => NatRedTmEq.whredR Rtu |}.
Next Obligation.
  now destruct h.
Qed.

Section Monad.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.
  Lemma Nat_SplitSNat : forall {Γ t u}, NatRedTmEq Γ t u -> Split_Rel SNatRedTmEq Γ t u.
  Proof.
    intros Γ t u h.
    induction h as [t u d h].
    now exists d.
  Qed.
  Lemma SplitSNat_Nat : forall {Γ t u}, Split_Rel SNatRedTmEq Γ t u -> NatRedTmEq Γ t u.
  Proof.
    intros Γ t u h.
    exists h.(dtree).
    eapply h.
  Qed.
End Monad.


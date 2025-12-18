(** * LogRel.LogicalRelation.Irrelevance: symmetry and irrelevance of the logical relation. *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.
Set Primitive Projections.


Section Symmetry.
  Context `{GenericTypingProperties}.

  Section SymLemmas.

  Universe i j k l v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record Ssym {Γ l A B} {R : [LogRel@{i j k l} l | Γ ||- A ≅ B]} :=
    { SsymRed : [LogRel@{i j k l} l | Γ ||- B ≅ A] ;
      SsymRedTm : forall {t u}, [Γ ||-S<l> t ≅ u : _ | SsymRed] <≈> [Γ ||-S<l> u ≅ t : _ | R] }.

  Arguments Ssym : clear implicits.
  Arguments Ssym {_ _ _ _}.

  Definition symPoly {Γ l A A' B B'} (ΠA : PolyRed Γ l A A' B B')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]), Ssym (PolyRed.shpRed ΠA ρ wfΔ))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ wfΔ | Δ ||- a ≅ b : _]),
        dover (PolyRed.posRed ΠA ρ wfΔ ha) (fun _ _ _ => Ssym))
      : PolyRed Γ l A' A B' B.
  Proof.
    unshelve econstructor.
    * intros; now unshelve eapply SsymRed, ihdom.
    * intros * ha; cbn in *.
      eapply (Split_bind_return (PolyRed.posRed ΠA ρ wfΔ (fst (SsymRedTm (ihdom Δ ρ wfΔ)) ha))).
      intros; now eapply ihcod.
  Defined.

  Definition symParamRedTy {T Γ l A A'} (ΠA : ParamRedTy T Γ l A A')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]), Ssym (PolyRed.shpRed ΠA ρ wfΔ))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ wfΔ | Δ ||- a ≅ b : _]),
        dover (PolyRed.posRed ΠA ρ wfΔ ha) (fun _ _ _ => Ssym))
      : ParamRedTy T Γ l A' A.
  Proof.
    destruct ΠA; cbn in *; unshelve econstructor.
    5,6: eassumption.
    1,2: now symmetry.
    now eapply symPoly.
  Defined.

  Section SymΠ.
    Context {Γ l A A'} (ΠA : [Γ ||-Π<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]), Ssym (PolyRed.shpRed ΠA ρ wfΔ))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΠA ρ wfΔ | Δ ||- a ≅ b : _]),
          dover (PolyRed.posRed ΠA ρ wfΔ ha) (fun _ _ _ => Ssym)).

    Let symΠ := symParamRedTy ΠA ihdom ihcod.

    Definition symIsLRFun {t} : isLRFun ΠA t <≈> isLRFun symΠ t.
    Proof.
      split.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros.
          specialize (Rbody Δ b a ρ wfΔ (fst (SsymRedTm _) ha)).
          eapply (dSplit_bind_return Rbody).
          intros Ξ wfΞ ρΞ oha' oRbody ohA; cbn in *.
          now unshelve eapply SirrLR, ihcod, Rbody.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros ??????.
          specialize (Rbody Δ b a ρ wfΔ (snd (SsymRedTm _) ha)).
          eapply (dSplit_bind_return Rbody).
          intros Ξ wfΞ ρΞ oha' oRbody ohA; cbn in *.
          now unshelve eapply ihcod, SirrLR, Rbody.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
    Qed.

    Definition symPiRedTm {t} : PiRedTm ΠA t <≈> PiRedTm symΠ t.
    Proof.
      split; intros [?? ?%symIsLRFun]; econstructor; tea.
      all: eapply redtmwf_conv; tea; apply ParamRedTy.eq.
    Defined.

    Definition symPiRedTmEq {t u} : PiRedTmEq ΠA t u <≈> PiRedTmEq symΠ u t.
    Proof.
      split; intros []; unshelve econstructor; try now eapply symPiRedTm.
      1,3: cbn; eapply convtm_conv; [now symmetry| eapply PiRedTy.eq].
      - intros Δ a b ρ wfΔ hab; cbn in *.
        specialize (eqApp Δ b a ρ wfΔ (fst (SsymRedTm _) hab)).
        eapply (dSplit_bind_return eqApp).
        intros Ξ wfΞ ρΞ oha' oeqApp ohA; cbn in *.
        now unshelve eapply SirrLR, ihcod, eqApp.
      - intros Δ a b ρ wfΔ hab; cbn in *.
        specialize (eqApp Δ b a ρ wfΔ (snd (SsymRedTm _) hab)).
        eapply (dSplit_bind_return eqApp).
        intros Ξ wfΞ ρΞ oha' oeqApp ohA; cbn in *.
        now unshelve eapply ihcod, SirrLR, eqApp.
    Qed.

    Definition symLRΠ : Ssym (LRPi' ΠA).
    Proof. exists (LRPi' symΠ); intros; cbn; split; eapply symPiRedTmEq. Qed.
  End SymΠ.


  Lemma symNe {Γ A B} : [Γ ||-ne A ≅ B] -> [Γ ||-ne B ≅ A].
  Proof.
    intros []; unshelve econstructor.
    3,4: tea.
    now symmetry.
  Defined.

  Lemma symNeNf {Γ t u A} : [Γ ||-NeNf t ≅ u : A] -> [Γ ||-NeNf u ≅ t : A].
  Proof.
    intros []; econstructor; tea; now symmetry.
  Qed.

  Lemma symNatRedTmEq {Γ} :
    (forall t u, NatRedTmEq Γ t u -> NatRedTmEq Γ u t) ×
    (forall t u, NatPropEq Γ t u -> NatPropEq Γ u t).
  Proof.
    eapply NatRedEqInduction.
    - intros; econstructor; tea; now symmetry.
    - constructor.
    - intros; now constructor.
    - intros; constructor; now eapply symNeNf.
  Qed.

  Lemma symBoolPropEq {Γ} :
    forall t u, BoolPropEq Γ t u -> BoolPropEq Γ u t.
  Proof.
    intros ?? []; econstructor.
    now eapply symNeNf.
  Qed.

  Lemma symBoolRedTmEq {Γ} :
    forall t u, BoolRedTmEq Γ t u -> BoolRedTmEq Γ u t.
  Proof.
    intros ?? []; econstructor; tea.
    2: now eapply symBoolPropEq.
    now symmetry.
  Qed.
 

  Section SymΣ.
    Context {Γ l A A'} (ΣA : [Γ ||-Σ<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ]), Ssym (PolyRed.shpRed ΣA ρ wfΔ))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΣA ρ wfΔ | Δ ||- a ≅ b : _]), dover (PolyRed.posRed ΣA ρ wfΔ ha) (fun _ _ _ => Ssym)).

    Let symΣ := symParamRedTy ΣA ihdom ihcod.

    Definition symIsLRPair {t} : isLRPair ΣA t <≈> isLRPair symΣ t.
    Proof.
      split.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea.
            assert [|-Γ] as wfΓ by gtyping.
            set (hΣA := PolyRed.posRed ΣA wk_id wfΓ (r1 _ wk_id _)).
            unshelve eapply (Split_bind_convty hΣA).
            intros Δ wfΔ ρ ohΣA.
            erewrite 2!eq_subst_scons.
            symmetry; now eapply escapeEq, hΣA.
          + intros; cbn.
            specialize (r2 _ ρ h).
            eapply (dSplit_bind_return r2).
            intros Ξ wfΞ ρΞ oha' or2 ohA; cbn in *.
            now unshelve eapply SirrLR, ihcod, SirrLR, r2.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea.
            assert [|-Γ] as wfΓ by gtyping.
            set (hsymΣ := PolyRed.posRed symΣ wk_id wfΓ (r1 _ wk_id _)).
            unshelve eapply (Split_bind_convty hsymΣ).
            intros Δ wfΔ ρ ohsymΣ.
            erewrite 2!eq_subst_scons.
            symmetry; now eapply escapeEq, hsymΣ.
          + intros; cbn.
            specialize (r2 _ ρ h).
            eapply (dSplit_bind_return r2).
            intros Ξ wfΞ ρΞ oha' or2 ohA; cbn in *.
            now unshelve eapply ihcod, SirrLR, r2.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
    Qed.

    Definition symSigRedTm {t} : SigRedTm ΣA t <≈> SigRedTm symΣ t.
    Proof.
      split; intros [?? ?%symIsLRPair]; econstructor; tea.
      all: eapply redtmwf_conv; tea; apply ParamRedTy.eq.
    Defined.

    Definition symSigRedTmEq {t u} : SigRedTmEq ΣA t u <≈> SigRedTmEq symΣ u t.
    Proof.
      split; intros []; unshelve econstructor; try now eapply symSigRedTm.
      3,5: cbn; eapply convtm_conv; [now symmetry| eapply PiRedTy.eq].
      1,2: cbn; intros; now eapply ihdom.
      + intros; cbn in *.
        specialize (eqSnd _ ρ h).
        eapply (dSplit_bind_return eqSnd).
        intros Ξ wfΞ ρΞ oha' oeqSnd ohA; cbn in *.
        now unshelve eapply SirrLR, ihcod, SirrLR, eqSnd.
      + intros; cbn in *.
        specialize (eqSnd _ ρ h).
        eapply (dSplit_bind_return eqSnd).
        intros Ξ wfΞ ρΞ oha' oeqSnd ohA; cbn in *.
        now unshelve eapply ihcod, SirrLR, eqSnd.
    Qed.

    Definition symLRΣ : Ssym (LRSig' ΣA).
    Proof. exists (LRSig' symΣ); intros; cbn; split; eapply symSigRedTmEq. Qed.
  End SymΣ.

  Section SymId.
  Context {Γ l A B} (IA: [Γ ||-Id< l > A ≅ B]) (ihdom:  Ssym (IdRedTy.tyRed IA)).

  Lemma symId : [Γ ||-Id<l> B ≅ A].
  Proof.
    destruct IA; unshelve econstructor.
    8,9: tea.
    * now eapply ihdom.
    * now symmetry.
    * now eapply ihdom.
    * now eapply ihdom.
    * constructor.
      1: intros ?? ?%ihdom; eapply ihdom; cbn in *; now symmetry.
      intros ??? ?%ihdom ?%ihdom; eapply ihdom; cbn in *; now etransitivity.
  Defined.

  #[local] Instance : PER _ := IA.(IdRedTy.tyPER).
  #[local] Instance : PER _ := symId.(IdRedTy.tyPER).

  Lemma symIdPropEq {t u} : IdPropEq IA t u <≈> IdPropEq symId u t.
  Proof.
    pose proof (escapeEq (IA.(IdRedTy.tyRed))).
    split; intros []; constructor; tea.
    - etransitivity; tea; now symmetry.
    - etransitivity; tea; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.lhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.lhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.rhsRed]; now symmetry.
    - eapply ihdom; etransitivity;[| eapply IdRedTy.rhsRed]; now symmetry.
    - eapply symNeNf, NeNf.conv_; tea; eapply IdRedTy.eq.
    - etransitivity; tea.
    - etransitivity; tea.
    - eapply ihdom; etransitivity; [|apply symId.(IdRedTy.lhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.lhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.rhsRed)]; now symmetry.
    - eapply ihdom; etransitivity;[| apply symId.(IdRedTy.rhsRed)]; now symmetry.
    - eapply symNeNf, NeNf.conv_; tea; eapply IdRedTy.eq.
  Qed.

  Lemma symIdRedTmEq {t u} : IdRedTmEq IA t u <≈> IdRedTmEq symId u t.
  Proof.
    split; intros [????? ?%symIdPropEq]; econstructor; tea.
    3,6: eapply convtm_conv; [now symmetry|]; eapply IdRedTy.eq.
    all: eapply redtmwf_conv; tea; eapply IdRedTy.eq.
  Qed.

  Lemma symLRId : Ssym (LRId' IA).
  Proof.
    exists (LRId' symId).
    intros; split; eapply symIdRedTmEq.
  Qed.

  End SymId.

  End SymLemmas.

  Arguments Ssym : clear implicits.
  Arguments Ssym {_ _ _ _}.

  Theorem symLR_rec@{h i j k l v} {l}
    (ih : forall l', l' << l -> forall {Γ A B} (R : [Γ ||-S<l'> A ≅ B]), Ssym@{h i j k v} R)
    {Γ A B} (R : [Γ ||-S<l> A ≅ B]) : Ssym@{i j k l v} R.
  Proof.
    revert ih; indLR R.
    - intros h ih; unshelve econstructor.
      + destruct h; apply LRU_; now unshelve econstructor.
      + cbn; intros ??; split; intros []; cbn in *.
        all: unshelve econstructor; tea;[now symmetry|]; cbn.
        1,2: eapply redTyRecBwd.
        1,2: unshelve eapply SsymRed, ih, URedTy.lt.
        1,2: now eapply redTyRecFwd.
    - intros h _ ; unshelve econstructor.
      1: now eapply LRne_, symNe.
      + pose proof (convty_term (convtm_convneu UnivPos (neRedTy.eq h))).
        cbn; intros ??; split; intros []; cbn in *.
        all: unshelve econstructor; cbn.
        5,6,8,9: eapply redtmwf_conv;tea; now symmetry.
        1,2: eapply convneu_conv; [now symmetry|]; tea; now symmetry.
    - intros ΠA ihdom ihcod ih.
      eapply symLRΠ.
      all: intros; eauto.
      intros Ξ ρ' hover hΞ.
      now unshelve eapply ihcod.
    - intros NA _; unshelve econstructor.
      + eapply LRNat_; destruct NA; now econstructor.
      + intros; cbn; split; eapply symNatRedTmEq.
    - intros BA _; unshelve econstructor.
      + eapply LRBool_; destruct BA; now econstructor.
      + intros; cbn; split; eapply symBoolRedTmEq.
    - intros EA _; unshelve econstructor.
      + eapply LREmpty_; destruct EA; now econstructor.
      + intro; cbn; split; intros []; econstructor; tea; now eapply symNeNf.
    - intros ΣA ihdom ihcod ih; eapply symLRΣ; intros; eauto.
      intros Ξ ρ' hover hΞ.
      now unshelve eapply ihcod.
    - intros IA ihdom ih; eapply symLRId; eauto.
  Qed.


  Theorem symLR0@{i j k l v} : forall {Γ A B} (R : [Γ ||-S<zero> A ≅ B]), Ssym@{i j k l v} R.
  Proof.
    eapply symLR_rec; intros ? h; inversion h.
  Qed.

  Theorem SsymLR@{h i j k l v} : forall {l Γ  A B} (R : [Γ ||-S<l> A ≅ B]), Ssym@{i j k l v} R.
  Proof.
    intros []; [intros; eapply symLR0| apply symLR_rec].
    intros ? h; inversion h; intros; eapply symLR0.
  Qed.

End Symmetry.


Section WSymmetry.
  Context `{GenericTypingProperties}.


  Universe i j k l v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record sym {Γ l A B} {R : WLRAdequate@{i j k l} Γ l A B} :=
    { symRed : WLRAdequate@{i j k l} Γ l B A ;
      symRedTm : forall {t u}, [Γ ||-<l> t ≅ u : _ | symRed] <≈> [Γ ||-<l> u ≅ t : _ | R] }.

  Arguments sym : clear implicits.
  Arguments sym {_ _ _ _}.

  Theorem symLR : forall {l Γ A B} (R : [Γ ||-<l> A ≅ B]), sym R.
  Proof.
    intros ?????.
    unshelve econstructor.
    + eapply (Split_bind_return R).
      intros ??? oR.
      eapply SsymLR.
      now eapply R.
    + intros t u; split;
      intros Rtu; eapply (dSplit_bind_return Rtu);
      intros ??? oR' oRtu oR;
      now unshelve eapply SsymLR, SirrLR, Rtu.
  Qed.

End WSymmetry.













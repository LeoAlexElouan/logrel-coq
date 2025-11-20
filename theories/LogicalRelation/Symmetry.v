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

  Record sym {Γ l A B} {R : [LogRel@{i j k l} l | Γ ||- A ≅ B]} :=
    { symRed : [LogRel@{i j k l} l | Γ ||- B ≅ A] ;
      symRedTm : forall {t u}, [Γ ||-<l> t ≅ u : _ | symRed] <≈> [Γ ||-<l> u ≅ t : _ | R] }.

  Arguments sym : clear implicits.
  Arguments sym {_ _ _ _}.

  Definition symPoly {Γ l A A' B B'} (ΠA : PolyRed Γ l A A' B B')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), dover (PolyRed.posRed ΠA ρ h ha) (fun _ _ => sym))
      : PolyRed Γ l A' A B' B.
  Proof.
    unshelve econstructor.
    * intros; now unshelve eapply symRed, ihdom.
    * intros * ha; cbn in *.
      exists (PolyRed.posRed ΠA ρ h (fst (symRedTm (ihdom Δ ρ h)) ha)).(dtree).
      intros; now eapply ihcod.
  Defined.

  Definition symParamRedTy {T Γ l A A'} (ΠA : ParamRedTy T Γ l A A')
    (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
    (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
      (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), dover (PolyRed.posRed ΠA ρ h ha) (fun _ _ => sym))
      : ParamRedTy T Γ l A' A.
  Proof.
    destruct ΠA; cbn in *; unshelve econstructor.
    5,6: eassumption.
    1,2: now symmetry.
    now eapply symPoly.
  Defined.

  Section SymΠ.
    Context {Γ l A A'} (ΠA : [Γ ||-Π<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΠA ρ h))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : _]), dover (PolyRed.posRed ΠA ρ h ha) (fun _ _ => sym)).

    Let symΠ := symParamRedTy ΠA ihdom ihcod.

    Definition symIsLRFun {t} : isLRFun ΠA t <≈> isLRFun symΠ t.
    Proof.
      split.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros.
          specialize (Rbody Δ b a ρ h (fst (symRedTm _) ha)).
          eapply dSplit_bind; [clear Rbody| apply Rbody].
          intros Ξ ρ' hover hover' Rbody; cbn in *.
          eapply ihcod, Rbody.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???? Rbody|].
        * constructor; tea.
          1: etransitivity; tea; eapply ParamRedTy.eqdom.
          intros ? a b ρ h ha.
          specialize (Rbody Δ b a ρ h (snd (symRedTm _) ha)).
          eapply dSplit_bind; [clear Rbody| apply Rbody].
          intros Ξ ρ' hover hover' Rbody; cbn in *.
          eapply ihcod, irrLR, Rbody.
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
      - intros Δ a b ρ h hab; cbn in *.
        specialize (eqApp Δ b a ρ h (fst (symRedTm _) hab)).
        eapply dSplit_bind; [clear eqApp| apply eqApp].
        intros Ξ ρ' hover hover' eqApp; cbn in *.
        eapply ihcod, eqApp.
      - intros Δ a b ρ h hab; cbn in *.
        specialize (eqApp Δ b a ρ h (snd (symRedTm _) hab)).
        eapply dSplit_bind; [clear eqApp| apply eqApp].
        intros Ξ ρ' hover hover' eqApp; cbn in *.
        eapply ihcod, irrLR, eqApp.
    Qed.

    Definition symLRΠ : sym (LRPi' ΠA).
    Proof. exists (LRPi' symΠ); intros; cbn; split; eapply symPiRedTmEq. Qed.
  End SymΠ.


  Lemma symNe {Γ A B} : [Γ ||-Sne A ≅ B] -> [Γ ||-Sne B ≅ A].
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
    (forall t u, SNatRedTmEq Γ t u -> SNatRedTmEq Γ u t) ×
    (forall t u, NatRedTmEq Γ t u -> NatRedTmEq Γ u t) ×
    (forall t u, NatPropEq Γ t u -> NatPropEq Γ u t).
  Proof.
    eapply (NatRedEqInduction) with
      (P:= fun Γ t u _ => SNatRedTmEq Γ u t)
      (P1:= fun Γ t u _ => NatRedTmEq Γ u t)
      (P0:= fun Γ t u _ => NatPropEq Γ u t).
    - intros; econstructor; tea; now symmetry.
    - constructor.
    - intros; now constructor.
    - intros; constructor; now eapply symNeNf.
    - intros; now constructor.
  Qed.

  Lemma symBoolPropEq {Γ} :
    forall t u, BoolPropEq Γ t u -> BoolPropEq Γ u t.
  Proof.
    intros ?? []; econstructor.
    now eapply symNeNf.
  Qed.

  Lemma symBoolRedTmEq {Γ} :
    forall t u, SBoolRedTmEq Γ t u -> SBoolRedTmEq Γ u t.
  Proof.
    intros ?? []; econstructor; tea.
    2: now eapply symBoolPropEq.
    now symmetry.
  Qed.


  Section SymΣ.
    Context {Γ l A A'} (ΣA : [Γ ||-Σ<l> A ≅ A'])
      (ihdom: forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), sym (PolyRed.shpRed ΣA ρ h))
      (ihcod: forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
        (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a ≅ b : _]), dover (PolyRed.posRed ΣA ρ h ha) (fun _ _ => sym)).

    Let symΣ := symParamRedTy ΣA ihdom ihcod.

    Definition symIsLRPair {t} : isLRPair ΣA t <≈> isLRPair symΣ t.
    Proof.
      split.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea.
            apply Rel_PSh_root.
            assert [|-Γ] as hΓ by gtyping.
            pose proof (PolyRed.posRed ΣA wk_id hΓ (r1 _ wk_id _)) as hSplit; revert hSplit.
            eapply (split_bind_alg convty_shf).
            intros Δ ρ.
            erewrite 2!eq_subst_scons.
            intros hLR.
            symmetry; now eapply escapeEq.
          + intros; cbn.
            specialize (r2 _ ρ h).
            eapply dSplit_bind; [clear r2| apply r2].
            intros Ξ ρ' hover hover' r2; cbn in *.
            eapply ihcod, irrLR, r2.
        * constructor; eapply convneu_conv; tea; eapply ParamRedTy.eq.
      - intros [???????? r1 r2|].
        * unshelve eapply PairLRPair; tea.
          2: etransitivity; tea; eapply ParamRedTy.eqdom.
          + intros; now eapply ihdom.
          + etransitivity; tea.
            apply Rel_PSh_root.
            assert [|-Γ] as hΓ by gtyping.
            pose proof (PolyRed.posRed symΣ wk_id hΓ (r1 _ wk_id _)) as hSplit; revert hSplit.
            apply (split_bind_alg convty_shf).
            intros Δ ρ.
            erewrite 2!eq_subst_scons.
            intros hLR.
            symmetry; now eapply escapeEq.
          + intros; cbn.
            specialize (r2 _ ρ h).
            eapply dSplit_bind; [clear r2| apply r2].
            intros Ξ ρ' hover hover' r2; cbn in *.
            eapply ihcod, irrLR, r2.
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
        eapply dSplit_bind; [clear eqSnd| apply eqSnd].
        intros Ξ ρ' hover hover' eqSnd; cbn in *.
        eapply ihcod, irrLR, eqSnd.
      + intros; cbn in *.
        specialize (eqSnd _ ρ h).
        eapply dSplit_bind; [clear eqSnd| apply eqSnd].
        intros Ξ ρ' hover hover' eqSnd; cbn in *.
        eapply ihcod, irrLR, eqSnd.
    Qed.

    Definition symLRΣ : sym (LRSig' ΣA).
    Proof. exists (LRSig' symΣ); intros; cbn; split; eapply symSigRedTmEq. Qed.
  End SymΣ.

  Section SymId.
  Context {Γ l A B} (IA: [Γ ||-SId< l > A ≅ B]) (ihdom:  sym (IdRedTy.tyRed IA)).

  Lemma symId : [Γ ||-SId<l> B ≅ A].
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

  Lemma symIdRedTmEq {t u} : SIdRedTmEq IA t u <≈> SIdRedTmEq symId u t.
  Proof.
    split; intros [????? ?%symIdPropEq]; econstructor; tea.
    3,6: eapply convtm_conv; [now symmetry|]; eapply IdRedTy.eq.
    all: eapply redtmwf_conv; tea; eapply IdRedTy.eq.
  Qed.

  Lemma symLRId : sym (LRId' IA).
  Proof.
    exists (LRId' symId).
    intros; split; eapply symIdRedTmEq.
  Qed.

  End SymId.

  End SymLemmas.

  Arguments sym : clear implicits.
  Arguments sym {_ _ _ _}.

  Theorem symLR_rec@{h i j k l v} {l}
    (ih : forall l', l' << l -> forall {Γ A B} (R : [Γ ||-<l'> A ≅ B]), sym@{h i j k v} R)
    {Γ A B} (R : [Γ ||-<l> A ≅ B]) : sym@{i j k l v} R.
  Proof.
    revert ih; indLR R.
    - intros h ih; unshelve econstructor.
      + destruct h; apply LRU_; now unshelve econstructor.
      + cbn; intros ??; split; intros []; cbn in *.
        all: unshelve econstructor; tea;[now symmetry|]; cbn.
        1,2: eapply redTyRecBwd.
        1,2: unshelve eapply symRed, ih, URedTy.lt.
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
      intros Ξ ρ' hover.
      specialize (ihcod Δ a b ρ h ha Ξ ρ' hover); now apply ihcod.
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
      intros Ξ ρ' hover.
      specialize (ihcod Δ a b ρ h ha Ξ ρ' hover); now apply ihcod.
    - intros IA ihdom ih; eapply symLRId; eauto.
  Qed.


  Theorem symLR0@{i j k l v} : forall {Γ A B} (R : [Γ ||-<zero> A ≅ B]), sym@{i j k l v} R.
  Proof.
    eapply symLR_rec; intros ? h; inversion h.
  Qed.

  Theorem symLR@{h i j k l v} : forall {l Γ  A B} (R : [Γ ||-<l> A ≅ B]), sym@{i j k l v} R.
  Proof.
    intros []; [intros; eapply symLR0| apply symLR_rec].
    intros ? h; inversion h; intros; eapply symLR0.
  Qed.

End Symmetry.


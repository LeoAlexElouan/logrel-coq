From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Def Induction Escape Irrelevance Symmetry.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.
Set Primitive Projections.


Section Transitivity.
  Context `{GenericTypingProperties}.

  Section TransitivityLemmas.
  Universe i j k l i' j' k' l' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record Strans {Γ l1 l2 A B C}
   {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
   {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
  := {
    StransRed : [LogRel@{i j k l} l1 | Γ ||- A ≅ C] ;
    StransRedTm : forall t u v,
      [_ ||-S<l1> t ≅ u : _ | RAB] ->
      [_ ||-S<l2> u ≅ v : _ | RBC] ->
      [_ ||-S<l1> t ≅ v : _ | StransRed ]
  }.

  Arguments Strans {_ _ _ _ _ _}.

  Section ConducheHelper.
    Context {Γ l1 l2 A B C}
      {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
      {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
      (RAC : Strans RAB RBC)
      {a b} (hab : [Γ ||-S<l1> a ≅ b : _ | RAC.(StransRed)]).

      #[local]
      Lemma factor_right : [Γ ||-S<l2> a ≅ b : _ | RBC].
      Proof.
        now eapply (SsymLR RBC).(SsymRedTm), SirrLR, (SsymLR RAC.(StransRed)).(SsymRedTm).
      Qed.

      #[local]
      Lemma factor_left : [Γ ||-S<l1> a ≅ a : _ | RAB].
      Proof.
        eapply SirrLR, RAC.(StransRedTm).
        2: eapply SirrLR, (SsymLR RAB).(SsymRedTm).
        all: now eapply SirrLR.
      Qed.

      Definition factor : [Γ ||-S<l1> a ≅ a : _ | RAB] × [Γ ||-S<l2> a ≅ b : _ | RBC] :=
        (factor_left, factor_right).
  End ConducheHelper.



  Definition transPolyRed {Γ l1 l2 A1 B1 C1 A2 B2 C2}
    (PAB : PolyRed@{i j k l} Γ l1 A1 B1 A2 B2)
    (PBC : PolyRed@{i' j' k' l'} Γ l2 B1 C1 B2 C2)
    (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-S< l2 > B1⟨ρ⟩ ≅ C]),
      Strans (PolyRed.shpRed PAB ρ h) RBC)
    (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
      (ha : [PolyRed.shpRed PAB ρ h | Δ ||- a ≅ b: _]) l2 C,
      dover (PolyRed.posRed PAB ρ h ha) (fun Ξ _ ρΞ hSplit => forall (RBC : [Ξ ||-S< l2 > B2⟨wk_up _ ρ⟩[b..]⟨ρΞ⟩ ≅ C⟨ρΞ⟩]),
          Strans hSplit RBC)) :
    PolyRed@{i j k l} Γ l1 A1 C1 A2 C2.
  Proof.
    unshelve econstructor.
    - intros; unshelve eapply StransRed, ihdom.
      2: eapply PBC.(PolyRed.shpRed).
      all: tea.
    - cbn; intros ????? hab.
      pose proof (factor _ hab) as [haa hab'].
      pose proof (PBC.(PolyRed.posRed)) as hBC.
      specialize (hBC _ _ _ _ _ hab').
      unshelve eapply (Split_bind hBC); tea.
      intros Ξ wfΞ ρΞ ohBC.
      eapply (Split_wk_bind_return (PolyRed.posRed PAB ρ wfΔ haa) wfΞ ρΞ).
      intros Θ wfΘ ρΘ ohaa.
      unshelve eapply StransRed, ihcod.
      2:apply hBC.
      4: apply haa.
      2:now eapply overtree_PSh.
      all: easy.
  Qed.


  Context {Γ : context} {l1 l2 : TypeLevel} {A B C : term}.

  Definition transLRne (neAB : [Γ ||-ne A ≅ B]) (neBC : [Γ ||-ne B ≅ C]) :
    neRedTy.tyL neBC = neRedTy.tyR neAB ->
    Strans (LRne_ l1 neAB) (LRne_ l2 neBC).
  Proof.
    unshelve econstructor.
    + apply LRne_; destruct neAB, neBC; unshelve econstructor.
      3,4: tea.
      cbn in *; subst.
      etransitivity; tea.
    + cbn; intros ??? rtu ruv.
      pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
      assert [Γ |- neRedTy.tyL neBC ≅ neRedTy.tyL neAB].
      1:{ symmetry; destruct neBC, neAB; cbn in *; subst;
        eapply convty_term, convtm_convneu; tea; constructor. }
      destruct rtu, ruv; cbn in *; subst.
      econstructor; cbn; [tea|..].
      * eapply redtmwf_conv; tea.
      * etransitivity; tea; eapply convneu_conv; tea.
  Qed.


  Section transΠ.
    Context (ΠAB : [Γ ||-Π<l1> A ≅ B]) (ΠBC : [Γ ||-Π<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-S< l2 > (ParamRedTy.domR ΠAB)⟨ρ⟩ ≅ C]),
        Strans (PolyRed.shpRed ΠAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΠAB ρ h | Δ ||- a ≅ b: _]) l2 C, dover (PolyRed.posRed ΠAB ρ h ha)
          (fun Ξ wfΞ ρ' hSplit => forall (RBC : [Ξ ||-S< l2 > (ParamRedTy.codR ΠAB)⟨wk_up _ ρ⟩[b..]⟨ρ'⟩ ≅ C⟨ρ'⟩]),
            Strans hSplit RBC))
      (eqdom : ParamRedTy.domL ΠBC = ParamRedTy.domR ΠAB)
      (eqcod : ParamRedTy.codL ΠBC = ParamRedTy.codR ΠAB).

    Let eqΠ : outTyL ΠBC = outTyR ΠAB.
    Proof. cbn; now rewrite eqdom, eqcod. Qed.

    Definition transΠ : [Γ ||-Π<l1> A ≅ C].
    Proof.
      destruct ΠAB, ΠBC; econstructor; tea; cbn in *; subst.
      1,2: now etransitivity.
      now eapply transPolyRed.
    Defined.

    #[local]
    Definition piRedTmLeft {t} : PiRedTm ΠAB t -> PiRedTm transΠ t.
    Proof.
      intros [?? isfun]; cbn in *; econstructor; tea.
      destruct isfun as [????? eqbody| | |]; constructor; tea.
      intros *.
      eapply SirrLR in ha as ha'.
      specialize (eqbody Δ a b ρ wfΔ ha').
      eapply (dSplit_bind_return eqbody).
      intros Ξ wfΞ ρΞ oha' oeqbody ohA; cbn in *.
      now unshelve eapply SirrLR, eqbody.
    Defined.

    #[local]
    Definition piRedTmRight {t} : PiRedTm ΠBC t -> PiRedTm transΠ t.
    Proof.
      intros [?? isfun]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΠ; symmetry; eapply ParamRedTy.eq.
      destruct isfun as [????? eqbody| | |]; constructor; tea.
      - etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      - intros ??? ρ h hab.
        cbn in *; destruct ΠAB as [domA domB' codA codB' redA redBl eqdomAB eqAB polyRedAB]; cbn in *; subst; cbn.
        unshelve epose proof (factor (ihdom _ ρ h _ _ (PolyRed.shpRed ΠBC ρ h)) _)
          as [haa hab'].
        3: eapply SirrLR, hab.
        destruct ΠBC as [domB domC codB codC redBr redC eqdomBC eqBC polyRedBC]; cbn in *.
        eassert ([_ | Δ ||- a ≅ a : term_decl domB⟨ρ⟩ ≅ _]) as haa' by eapply SirrLR, SsymLR, haa.
        specialize (eqbody Δ a b ρ h hab') as eqab; cbn in *.
        specialize (eqbody Δ a a ρ h haa') as eqaa; cbn in *.
        clear eqbody.
        unshelve eapply (dSplit_bind eqab).
        intros Ξ wfΞ ρΞ ohab' oeqab.
        unshelve eapply (dSplit_wk_bind eqaa wfΞ ρΞ).
        intros Θ wfΘ ρΘ ohaa' oeqaa.
        unshelve eapply (Split_wk_bind_return (PolyRed.posRed polyRedAB ρ h haa) wfΘ (ρΘ ∘w ρΞ)).
        intros Ω wfΩ ρΩ ohaa oirr; cbn in *.
        eapply SirrLR, ihcod, eqab; clear oirr.
        eapply (SsymLR _).(SsymRedTm), SirrLR.
        eapply eqaa.
        Unshelve.
        all: tea.
        + now rewrite wk_comp_assoc; apply overtree_PSh.
        + now eapply overtree_PSh.
        + clear oirr. now eapply overtree_PSh.
        + now rewrite wk_comp_assoc.
        + now rewrite wk_comp_assoc; apply overtree_PSh.
      - cbn in *; etransitivity; tea; rewrite eqΠ; eapply ParamRedTy.eq.
      - cbn in *; etransitivity; tea; rewrite eqΠ; eapply ParamRedTy.eq.
      - eapply convneu_conv; tea; cbn; rewrite eqΠ; symmetry; apply ParamRedTy.eq.
    Defined.

    Definition transLRΠ : Strans (LRPi' ΠAB) (LRPi' ΠBC).
    Proof.
      exists (LRPi' transΠ); intros ??? [rt ru eqtu appl] [ru' rv equv appr].
      pose proof (equ := whredtm_det (whredtm ru) (whredtm ru')); cbn in equ.
      unshelve econstructor.
      - now eapply piRedTmLeft.
      - now eapply piRedTmRight.
      - cbn; etransitivity; tea.
        replace (PiRedTmEq.nf ru) with (PiRedTmEq.nf ru').
        eapply convtm_conv; tea; cbn in *; rewrite eqΠ; symmetry;apply ParamRedTy.eq.
      - intros ????? hab.
        cbn in *; destruct ΠAB as [domA domB' codA codB' redA redBl eqdomAB eqAB polyRedAB]; cbn in *; subst; cbn.
        unshelve epose proof (factor (ihdom _ ρ h _ _ (PolyRed.shpRed ΠBC ρ h)) _) as [haa hab'].
        3: eapply SirrLR, hab.
        destruct ΠBC as [domB domC codB codC redBr redC eqdomBC eqBC polyRedBC]; cbn in *.
        specialize (appl Δ a a ρ h haa).
        specialize (appr Δ a b ρ h hab').
        unshelve eapply (dSplit_bind appl).
        intros Ξ wfΞ ρΞ ohaa oappl.
        unshelve eapply (dSplit_wk_bind_return appr wfΞ ρΞ).
        intros Θ wfΘ ρΘ ohab oappr oirr.
        eapply SirrLR, ihcod, appr; clear oirr.
        replace (PiRedTmEq.nf ru') with (PiRedTmEq.nf ru).
        eapply appl.
        Unshelve. all: tea; cbn in *.
        all: now apply overtree_PSh.
    Qed.

  End transΠ.

  Section transΣ.
    Context (ΣAB : [Γ ||-Σ<l1> A ≅ B]) (ΣBC : [Γ ||-Σ<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-S< l2 > (ParamRedTy.domR ΣAB)⟨ρ⟩ ≅ C]),
        Strans (PolyRed.shpRed ΣAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΣAB ρ h | Δ ||- a ≅ b: _]) l2 C, dover (PolyRed.posRed ΣAB ρ h ha)
        (fun Ξ wfΞ ρΞ hSplit => forall (RBC : [Ξ ||-S< l2 > (ParamRedTy.codR ΣAB)⟨wk_up _ ρ⟩[b..]⟨ρΞ⟩ ≅ C⟨ρΞ⟩]),
        Strans hSplit RBC))
      (eqdom : ParamRedTy.domL ΣBC = ParamRedTy.domR ΣAB)
      (eqcod : ParamRedTy.codL ΣBC = ParamRedTy.codR ΣAB).

    Let eqΣ : outTyL ΣBC = outTyR ΣAB.
    Proof. cbn; now rewrite eqdom, eqcod. Qed.

    Definition transΣ : [Γ ||-Σ<l1> A ≅ C].
    Proof.
      destruct ΣAB, ΣBC; econstructor; tea; cbn in *; subst.
      1,2: now etransitivity.
      now eapply transPolyRed.
    Defined.

    #[local]
    Definition sigRedTmLeft {t} : SigRedTm ΣAB t -> SigRedTm transΣ t.
    Proof.
      intros [?? ispair]; cbn in *; econstructor; tea.
      destruct ispair as [???????? rfst rsnd|].
      2:now constructor.
      unshelve eapply PairLRPair; tea.
      - intros ; now unshelve eapply SirrLR, rfst.
      - intros.
        specialize (rsnd Δ ρ h).
        eapply (dSplit_bind_return rsnd).
        intros Ξ wfΞ ρΞ oha' orsnd ohA; cbn in *.
        now unshelve eapply SirrLR, rsnd.
    Defined.

    #[local]
    Definition sigRedTmRight {t} : SigRedTm ΣBC t -> SigRedTm transΣ t.
    Proof.
      intros [?? ispair]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΣ; symmetry; eapply ParamRedTy.eq.
      destruct ispair as [???????? rfst rsnd|].
      2: constructor; eapply convneu_conv; tea; cbn; rewrite eqΣ; symmetry; apply ParamRedTy.eq.
      unshelve eapply PairLRPair; tea.
      1: intros; now unshelve now eapply (SsymLR _).(SsymRedTm), SirrLR, (SsymLR _).(SsymRedTm).
      1: etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      etransitivity; tea; cbn; destruct ΣAB as [???????? PAB]; cbn in *; subst.
      + (* erewrite 2!eq_subst_scons. *)
        assert ([|-Γ]) as wfΓ by gtyping.
        unshelve eassert (Split _) as hSplit
          by (unshelve eapply PAB.(PolyRed.posRed), (SsymLR _).(SsymRedTm), SirrLR, rfst;
          try eapply wfΓ; eapply wk_id); tea.
        rewrite 2wk_up_wk_id, 3wk_id_ren_on in hSplit.
        eapply (Split_bind_convty hSplit).
        intros Δ wfΔ ρ ohSplit.
        now eapply escapeTy, hSplit.
      + intros; cbn in *.
        specialize (rsnd Δ ρ h).
        eapply (dSplit_bind_return rsnd).
        intros Ξ wfΞ ρΞ oha' orsnd ohA; cbn in *.
        now unshelve eapply SsymLR, SirrLR, SsymLR,rsnd.
    Defined.

    Definition transLRΣ : Strans (LRSig' ΣAB) (LRSig' ΣBC).
    Proof.
      exists (LRSig' transΣ); intros ??? [rt ru eqtu fsttu sndtu] [ru' rv equv fstuv snduv].
      pose proof (equ := whredtm_det (whredtm ru) (whredtm ru')); cbn in equ.
      unshelve econstructor.
      - now eapply sigRedTmLeft.
      - now eapply sigRedTmRight.
      - intros.
        cbn in *; destruct ΣAB; cbn in *; subst; cbn.
        unshelve (eapply SirrLR, ihdom; [eapply fsttu|]).
        5: replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru'); now unshelve apply fstuv.
        tea.
      - cbn; etransitivity; tea.
        replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru').
        eapply convtm_conv; tea; cbn in *; rewrite eqΣ; symmetry;apply ParamRedTy.eq.
      - intros; cbn in *.
        destruct ΣAB as
          [domA domB' codA codB' redA redBl eqdomAB eqAB polyRedAB]; cbn in *; subst.
        destruct ΣBC as
          [domB domC codB codC redBr redC eqdomBC eqBC polyRedBC]; cbn in *.
        eassert ([_| Δ ||- _ ≅ tFst (SigRedTmEq.nf ru')⟨ρ⟩ : _ ≅ _]) as fsttu'
          by (replace (SigRedTmEq.nf ru') with (SigRedTmEq.nf ru); apply fsttu).
        specialize (sndtu Δ ρ h).
        specialize (snduv Δ ρ h).
        eapply (dSplit_bind sndtu).
        intros Ξ wfΞ ρΞ ofsttu osndtu.
        eapply (dSplit_wk_bind snduv wfΞ ρΞ).
        intros Θ wfΘ ρΘ ofstuv osnduv.
        eapply (Split_wk_bind_return (PolyRed.posRed polyRedAB ρ h fsttu') wfΘ (ρΘ∘w ρΞ)).
        intros Ω wfΩ ρΩ ofsttu' oirr; cbn in *.
        eapply SirrLR, ihcod, snduv; clear oirr.
        eapply SirrLR.
        replace (SigRedTmEq.nf ru') with (SigRedTmEq.nf ru).
        eapply sndtu.
        Unshelve. all: tea.
        + now eapply overtree_PSh.
        + rewrite wk_comp_assoc. now eapply overtree_PSh.
        + clear oirr. rewrite wk_comp_assoc. now eapply overtree_PSh.
        + now rewrite wk_comp_assoc.
        + now eapply overtree_PSh.
    Qed.

  End transΣ.

  Section transId.
  Context (IAB : [Γ ||-Id<l1> A ≅ B]) (IBC : [Γ ||-Id<l2> B ≅ C])
    (ihty: forall l2 C (RBC : [Γ ||-S< l2 > IdRedTy.tyR IAB ≅ C]), Strans (IdRedTy.tyRed IAB) RBC)
    (* (ihkr: forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (IdRedTy.tyR IAB)⟨ρ⟩ ≅ C]),
      trans (IdRedTy.tyKripke IAB ρ wfΔ) RBC) *)
    ( eqty: IdRedTy.tyL IBC = IdRedTy.tyR IAB )
    ( eqlhs: IdRedTy.lhsL IBC = IdRedTy.lhsR IAB )
    ( eqrhs: IdRedTy.rhsL IBC = IdRedTy.rhsR IAB ).

  Arguments IdRedTy.outTy _ /.

  Let eqId : IdRedTy.outTy IBC = tId (IdRedTy.tyR IAB) (IdRedTy.lhsR IAB) (IdRedTy.rhsR IAB).
  Proof. cbn; now rewrite eqty, eqlhs, eqrhs. Qed.

  Definition transId : [Γ ||-Id<l1> A ≅ C].
  Proof.
    unshelve econstructor.
    8: exact (IdRedTy.redL IAB).
    5: exact (IdRedTy.redR IBC).
    1: eapply ihty; rewrite <- eqty; eapply IdRedTy.tyRed.
    all: destruct IAB, IBC; cbn in *; subst; tea.
    - now etransitivity.
    - now eapply ihty.
    - now eapply ihty.
    - cbn; constructor.
      + intros ?? ?%(SirrLR tyRed) ; eapply (SirrLR _ tyRed); now symmetry.
      + intros ??? ?%(SirrLR tyRed) ?%(SirrLR tyRed); eapply (SirrLR _ tyRed); now etransitivity.
  Defined.

  Definition transIdPropEq {t u v} : IdPropEq IAB t u -> IdPropEq IBC u v -> IdPropEq transId t v.
  Proof.
    intros [|?? [?? conv]].
    - intros ruv; inversion ruv as [| ?? [?? whr%convneu_whne] ]; subst.
      2: inversion whr.
      constructor; cbn in *; destruct IAB as [????? rhsR], IBC ; cbn in *; subst; tea.
      2,4: now eapply SirrLR.
      + etransitivity; [|tea]; now eapply escapeEq.
      + eapply ihty; [|tea]; tea.
      + unshelve eapply ihty. 1: exact rhsR. all: tea.
    - intros ruv; inversion ruv as [|?? []]; subst.
      1: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      econstructor; cbn in *; destruct IAB, IBC; cbn in *; subst; tea.
      constructor; tea.
      1: now eapply ty_conv.
      etransitivity; tea; now eapply convneu_conv.
  Qed.

  Definition transIdRedTmEq {t u v} : [Γ ||-Id<l1> t ≅ u : _ | IAB] -> [Γ ||-Id<l2> u ≅ v : _ | IBC] ->
    [Γ ||-Id<l1> t ≅ v : _ | transId].
  Proof.
    intros rtu ruv; pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
    destruct rtu, ruv; cbn in *; subst; econstructor.
    + tea.
    + eapply redtmwf_conv; tea; rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + etransitivity; tea; eapply convtm_conv; tea.
      rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + now eapply transIdPropEq.
  Qed.

  Definition transLRId : Strans (LRId' IAB) (LRId' IBC).
  Proof. exists (LRId' transId). intros; now eapply transIdRedTmEq. Qed.

  End transId.

  End TransitivityLemmas.

  Arguments Strans : clear implicits.
  Arguments Strans {_ _ _ _ _ _}.

  Lemma transNatRedTmEq {Γ} :
    (forall t u, NatRedTmEq Γ t u -> forall v, NatRedTmEq Γ u v -> NatRedTmEq Γ t v) ×
    (forall t u, NatPropEq Γ t u -> forall v, NatPropEq Γ u v -> NatPropEq Γ t v).
  Proof.
    apply NatRedEqInduction.
    - intros * rL rR eq prop ih ? Ruv.
      set (Rtu := Build_NatRedTmEq _ _ rL rR eq prop).
      pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ; subst.
      depelim Ruv; cbn in *; econstructor; tea.
      + etransitivity; tea.
      + now eapply ih.
    - intros ? h; inversion h as [| | ?? [?? whz%convneu_whne]]; subst.
      1: constructor.
      inversion whz.
    - intros ??? ih ? h; inversion h as [| | ?? [?? whs%convneu_whne]]; subst.
      2: inversion whs.
      constructor; eauto.
    - intros ?? [?? conv] ? h; inversion h as [ | |??  []]; subst.
      1,2: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      do 2 econstructor; tea; now etransitivity.
  Qed.

  Lemma transBoolPropEq {Γ} :
    forall t u, BoolPropEq Γ t u -> forall v, BoolPropEq Γ u v -> BoolPropEq Γ t v.
  Proof.
    intros ?? [ | | ?? [?? conv]].
    1,2: easy.
    intros ? h; inversion h as [| | ?? []]; subst.
    1,2: symmetry in conv; eapply convneu_whne in conv; inversion conv.
    do 2 econstructor; tea; now etransitivity.
  Qed.

  Lemma transBoolRedTmEq {Γ} :
    forall t u, BoolRedTmEq Γ t u -> forall v, BoolRedTmEq Γ u v -> BoolRedTmEq Γ t v.
  Proof.
    intros ?? hL ? hR.
    pose proof (equ := whredtm_det (whredtmR hL) (whredtmL hR)); cbn in equ.
    destruct hL, hR; subst.
    econstructor; tea.
    - now etransitivity.
    - now eapply transBoolPropEq.
  Qed.

  Lemma transTreeRedTmEq {Γ} :
    forall veq t u, TreeRedTmEq.TreeTmEq Γ veq t u ->
      forall v, TreeRedTmEq.TreeTmEq Γ veq u v -> TreeRedTmEq.TreeTmEq Γ veq t v.
  Proof.
    intros ??? Rtu.
    induction Rtu as [??????? prop ih| |??????? Rtl ihRtl Rtr ihRtr| ?? [?? conv]].
    + intros v Ruv.
      induction u, v, Ruv as [u v nfL' nfR' redL' redR' eq' prop'] using TreeRedTmEq.TreeRedTmEq_destruct.
      set (Rtu := Build_TreeRedTmEq _ _ redL redR eq prop).
      set (Ruv := Build_TreeRedTmEq _ _ redL' redR' eq' prop').
      pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ; subst.
      econstructor; tea.
      - now etransitivity.
      - now eapply ih.
    + intros v Ruv; inversion Ruv as [ | | | ?? [?? whl%convneu_whne]]; subst.
      - constructor; now eapply transNatRedTmEq.
      - inversion whl.
    + intros v Ruv; inversion Ruv as [ | | | ?? [?? whn%convneu_whne]]; subst.
      - constructor; eauto.
        now eapply transNatRedTmEq.
      - inversion whn.
    + intros v Ruv; inversion Ruv as [ | | | ?? []]; subst.
      1,2 : symmetry in conv; eapply convneu_whne in conv; inversion conv.
      do 2 econstructor; tea; now etransitivity.
  Qed.

  Definition transLRU@{h i j k l h' i' j' k' l' v} {l1}
    (ih : forall l', l' << l1 ->
      forall Γ l2 A B C (RAB : [Γ ||-S<l'> A ≅ B]) (RBC : [Γ ||-S<l2> B ≅ C]),
        Strans@{h i j k h' i' j' k' v} RAB RBC)
    {Γ l2 A B C}
    (h : [Γ ||-U<l1> A ≅ B]) (h' : [Γ ||-U<l2> B ≅ C]) :
    Strans@{i j k l i' j' k' l' v} (LRU_ h) (LRU_ h').
  Proof.
    unshelve econstructor.
    + apply LRU_; destruct h, h'; now econstructor.
    + assert (eq : h.(URedTy.level) = h'.(URedTy.level)) by now destruct h.(URedTy.lt), h'.(URedTy.lt).
      cbn; intros ??? [? ru] [ru' rv]; unshelve econstructor; tea; cbn.
      * destruct rv; now econstructor.
      * cbn; etransitivity; tea.
        replace (URedTm.te ru) with (URedTm.te ru'); tea.
        refine (whredtm_det (whredtm ru') (whredtm ru)).
      * eapply redTyRecBwd; eapply ih.
        1: apply URedTy.lt.
        all: now eapply redTyRecFwd.
  Qed.

  Lemma transLR_rec@{h i j k l h' i' j' k' l' v} {l}
    (ih : forall l', l' << l ->
      forall Γ l2 A B C (RAB : [Γ ||-S<l'> A ≅ B]) (RBC : [Γ ||-S<l2> B ≅ C]),
        Strans@{h i j k h' i' j' k' v} RAB RBC)
    Γ l2 A B C (RAB : [Γ ||-S<l> A ≅ B]) (RBC : [Γ ||-S<l2> B ≅ C]) :
    Strans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    pose (i := invLREqL_whred' RAB RBC).
    revert ih l2 C RBC i; indLR RAB.
    - intros h ih ? ? ? [h']; subst; now eapply transLRU.
    - intros neAB _ ??? [neBC []]; subst; now eapply transLRne.
    - intros ΠAB ? ihdom ihcod ??? [ΠBC []]; cbn in *; subst; eapply transLRΠ; eauto.
      intros ???????? Ξ ρΞ hovera RBC. eapply ihdom. eapply ihcod.
    - intros NAB _ ??? [NBC]; subst; unshelve econstructor.
      + apply LRNat_; destruct NAB, NBC; now econstructor.
      + intros ???; cbn; intros ?; now eapply transNatRedTmEq.
    - intros BAB _ ??? [BBC]; subst; unshelve econstructor.
      + apply LRBool_; destruct BAB, BBC; now econstructor.
      + intros ???; cbn; intros ?; now eapply transBoolRedTmEq.
    - intros EAB _ ??? [EBC]; subst; unshelve econstructor.
      + apply LREmpty_; destruct EAB, EBC; now econstructor.
      + intros ???; cbn; intros Rtu Ruv.
        pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ.
        destruct Rtu as [???? []], Ruv as [???? []] ; econstructor; tea.
        constructor; tea; subst.
        now etransitivity.
    - intros TAB _ ??? [TBC]; subst; unshelve econstructor.
      + apply LRTree_; destruct TAB, TBC; now econstructor.
      + intros ???; cbn; intros ?; now eapply transTreeRedTmEq.
    - intros ΣAB ? ihdom ihcod ??? [ΣBC []]; cbn in *; subst; eapply transLRΣ; eauto.
      intros ???????? Ξ ρΞ hovera RBC. eapply ihdom. eapply ihcod.
    - intros IAB ihty ???? [IBC []]; cbn in *; subst.
      eapply transLRId; eauto.
  Qed.

  Theorem transLR0@{i j k l i' j' k' l' v}  {Γ l2 A B C} (RAB : [Γ ||-S<zero> A ≅ B]) (RBC : [Γ ||-S<l2> B ≅ C]) :
    Strans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    eapply transLR_rec; intros ? h; inversion h.
  Qed.

  Theorem StransLR@{h i j k l h' i' j' k' l' v} {Γ l1 l2 A B C}
    (RAB : [Γ ||-S<l1> A ≅ B]) (RBC : [Γ ||-S<l2> B ≅ C]) :
    Strans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    destruct l1; [eapply transLR0| apply transLR_rec].
    intros ? h; inversion h; intros; eapply transLR0.
  Qed.

End Transitivity.


Section WTransitivity.
  Context `{GenericTypingProperties}.


  Universe i j k l i' j' k' l' v.

  Notation "A <≈> B" := (prod@{v v} (A -> B) (B -> A)) (at level 90).

  Record trans {Γ l1 l2 A B C}
   {RAB : WLRAdequate@{i j k l} Γ l1 A B}
   {RBC : WLRAdequate@{i' j' k' l'} Γ l2 B C}
  := {
    transRed : WLRAdequate@{i j k l} Γ l1 A C;
    transRedTm : forall t u v,
      [_ ||-<l1> t ≅ u : _ | RAB] ->
      [_ ||-<l2> u ≅ v : _ | RBC] ->
      [_ ||-<l1> t ≅ v : _ | transRed ]
  }.

  Arguments trans {_ _ _ _ _ _}.
  Theorem transLR {Γ l1 l2 A B C}
      (RAB : [Γ ||-<l1> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
      trans RAB RBC.
  Proof.
    unshelve econstructor.
    + eapply (Split_bind RAB).
      intros Δ wfΔ ρ oRAB.
      eapply (Split_wk_bind_return RBC wfΔ ρ).
      intros Ξ wfΞ ρΞ oBC.
      eapply StransLR.
      - now eapply RAB, overtree_PSh, oRAB.
      - now eapply RBC.
    + intros ??? Rtu Ruv.
      eapply (dSplit_bind Rtu).
      intros Δ wfΔ ρ oRAB oRtu.
      eapply (dSplit_wk_bind_return Ruv wfΔ ρ).
      intros Ξ wfΞ ρ' oRBC oRuv oirr.
      eapply SirrLR, (StransLR _ _).(StransRedTm); clear oirr.
      - unshelve eapply Rtu; now try eapply overtree_PSh.
      - now unshelve now eapply Ruv.
  Qed.

End WTransitivity.

Instance SperLRTy `{GenericTypingProperties} {Γ l} : PER (LRAdequate Γ (LogRel l)).
Proof.
  constructor.
  - intros A B RAB; exact (SsymLR RAB).(SsymRed).
  - intros A B C RAB RBC; exact (StransLR RAB RBC).(StransRed).
Defined.

Instance perLRTy `{GenericTypingProperties} {Γ l} : PER (WLRAdequate Γ l).
Proof.
  constructor.
  - intros A B RAB; exact (symLR RAB).(symRed).
  - intros A B C RAB RBC; exact (transLR RAB RBC).(transRed).
Defined.

Section Consequences.
Context `{GenericTypingProperties}.

Lemma SlreflRedTm  {Γ l A B} {RAB : [Γ ||-S<l> A ≅ B]} {t u} : [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l> t ≅ t : _ | RAB].
Proof. intros Rtu; eapply SirrLR, (StransLR RAB _).(StransRedTm); tea; now eapply (SsymLR _).(SsymRedTm). Qed.

Lemma lreflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ t : _ | RAB].
Proof. intros Rtu; eapply irrLR, (transLR RAB _).(transRedTm); tea; now eapply (symLR _).(symRedTm). Qed.

Lemma SureflRedTm  {Γ l A B} {RAB : [Γ ||-S<l> A ≅ B]} {t u} : [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l> u ≅ u : _ | RAB].
Proof. intros Rtu%((SsymLR _).(SsymRedTm)); eapply (SsymLR _).(SsymRedTm); now eapply SlreflRedTm. Qed.

Lemma ureflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ u : _ | RAB].
Proof. intros Rtu%((symLR _).(symRedTm)); eapply (symLR _).(symRedTm); now eapply lreflRedTm. Qed.

Lemma SsymRedTm' {Γ l A B} {RAB : [Γ ||-S<l> A ≅ B]} {t u} : [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l> u ≅ t : _ | RAB].
Proof.
  intros Rtu. eapply SirrLR, (StransLR RAB _).(StransRedTm).
  2: now eapply (SsymLR _).(SsymRedTm).
  now eapply SureflRedTm.
Qed.

Lemma symRedTm' {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ t : _ | RAB].
Proof.
  intros Rtu. eapply irrLR, (transLR RAB _).(transRedTm).
  2: now eapply (symLR _).(symRedTm).
  now eapply ureflRedTm.
Qed.

Lemma SirrLRConv {Γ l A A' B B'} (RAB : [Γ ||-S<l> A ≅ B]) (RA : [Γ ||-S<l> A ≅ A']) (RB : [Γ ||-S<l> B ≅ B']) {t u} :
  [Γ ||-S<l> t ≅ u : _ | RA ] -> [Γ ||-S<l> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(SirrLR _ RAB)%((SsymLR _).(SsymRedTm))%SsymRedTm'; now eapply SirrLR.
Qed.

Lemma irrLRConv {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RA : [Γ ||-<l> A ≅ A']) (RB : [Γ ||-<l> B ≅ B']) {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(irrLR _ RAB)%((symLR _).(symRedTm))%symRedTm'; now eapply irrLR.
Qed.


Lemma SirrLRSym {Γ l A B} (RAB : [Γ ||-S<l> A ≅ B]) (RBA : [Γ ||-S<l> B ≅ A]) {t u} :
  [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l> t ≅ u : _ | RBA].
Proof. intros; now eapply SirrLRConv. Qed.

Lemma irrLRSym {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) (RBA : [Γ ||-<l> B ≅ A]) {t u} :
  [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RBA].
Proof. intros; now eapply irrLRConv. Qed.

Lemma SirrLRCum@{i j k l i' j' k' l' i0 j0 k0 l0} {Γ l0 l l' A A' B B'}
  (RAB : [LogRel@{i0 j0 k0 l0} l0 | Γ ||- A ≅ B])
  (RA : [LogRel@{i j k l} l | Γ ||- A ≅ A'])
  (RB : [LogRel@{i' j' k' l'} l' | Γ ||- B ≅ B']) {t u} :
  [Γ ||-S<l> t ≅ u : _ | RA ] -> [Γ ||-S<l'> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(SirrLR _ RAB)%((SsymLR _).(SsymRedTm))%SsymRedTm'; now eapply SirrLR.
Qed.

Lemma irrLRCum@{i j k l i' j' k' l' i0 j0 k0 l0} {Γ l0 l l' A A' B B'}
  (RAB : WLRAdequate@{i0 j0 k0 l0} Γ l0 A B)
  (RA : WLRAdequate@{i j k l} Γ l A A')
  (RB : WLRAdequate@{i' j' k' l'} Γ l' B B') {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l'> t ≅ u : _ | RB ].
Proof.
  intros Rtu.
  eapply irrLR, irrLRSym, irrLR, Rtu.
  Unshelve.
  2: symmetry.
  2,3 : eapply RAB.
Qed.

Lemma SirrLREq {Γ l A A' B B'} (RAB : [Γ ||-S<l> A ≅ B]) (RAB' : [Γ ||-S<l> A' ≅ B']) (eqA : A = A') {t u}
  : [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l> t ≅ u : _ | RAB'].
Proof. eapply SirrLRConv; subst; now eapply lrefl. Qed.

Lemma irrLREq {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RAB' : [Γ ||-<l> A' ≅ B']) (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RAB'].
Proof. eapply irrLRConv; subst; now eapply lrefl. Qed.

Lemma SirrLREqCum@{i j k l i' j' k' l'} {Γ l l' A A' B B'}
  (RAB : [LogRel@{i j k l} l | Γ ||- A ≅ B])
  (RAB' : [LogRel@{i' j' k' l'} l' | Γ ||- A' ≅ B'])
   (eqA : A = A') {t u}
  : [Γ ||-S<l> t ≅ u : _ | RAB] -> [Γ ||-S<l'> t ≅ u : _ | RAB'].
Proof. eapply SirrLRCum; subst; now eapply lrefl. Qed.

Lemma irrLREqCum@{i j k l i' j' k' l'} {Γ l l' A A' B B'}
  (RAB : WLRAdequate@{i j k l} Γ l A B)
  (RAB' : WLRAdequate@{i' j' k' l'} Γ l' A' B')
   (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l'> t ≅ u : _ | RAB'].
Proof. eapply irrLRCum; subst; now eapply lrefl. Qed.

End Consequences.

Instance SperLRTm `{GenericTypingProperties} {Γ l A B} (RAB : [Γ ||-S<l> A ≅ B]) :
  PER (RAB.(LRPack.eqTm)).
Proof.
  constructor.
  - intros ?? Rtu; now eapply SsymRedTm'.
  - intros ??? Rtu Ruv; eapply SirrLR, (StransLR _ _).(StransRedTm); tea.
    now eapply SirrLRConv.
    Unshelve. 2: now symmetry.
Qed.

Instance perLRTm `{GenericTypingProperties} {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) :
  PER (RAB.(LRPack.eqTm)).
Proof.
  constructor.
  - intros ?? Rtu; now eapply symRedTm'.
  - intros ??? Rtu Ruv; eapply irrLR, (transLR _ _).(transRedTm); tea.
    now eapply irrLRConv.
    Unshelve. 2: now symmetry.
Qed.


Instance SiperLRTm `{GenericTypingProperties} {Γ l} :
  IPER (LRAdequate Γ (LogRel l)) (fun _ => term) (fun _ _ RA => RA.(LRPack.eqTm)).
Proof.
  constructor.
  - intros; now eapply SsymLR.
  - intros; now eapply StransLR.
Qed.


Instance iperLRTm `{GenericTypingProperties} {Γ l} :
  IPER (WLRAdequate Γ l) (fun _ => term) (fun _ _ RA => RA.(LRPack.eqTm)).
Proof.
  constructor.
  - intros; now eapply symLR.
  - intros; now eapply transLR.
Qed.


Lemma kripkeLRlrefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B⟨wk_up A ρ⟩[b ..]].
Proof.
  eapply (Split_bind (hB _ _ _ _ _ hab)).
  intros Ξ wfΞ ρΞ ohab.
  eapply (Split_wk_bind_return (hB _ _ _ _ _ (urefl hab)) wfΞ ρΞ).
  intros Θ ρΘ ohbb hΘ.
  etransitivity.
  + eapply hB, overtree_PSh, ohab; tea.
  + symmetry; unshelve eapply hB.
    2: eapply urefl.
    2: apply hab.
    all: easy.
Qed.


(* Lemma LRlrefl `{GenericTypingProperties} {Γ} {wfΓ : [|-Γ]} {l A A' B B'}
  {hA : [wfΓ ||-<l> A ≅ A']}
  (hB : forall Δ wfΔ ρ ohA a b (hab : [cover hA Δ wfΔ ρ ohA | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  Δ wfΔ ρ ohA [a b] (hab : [cover hA Δ wfΔ ρ ohA | Δ ||- a ≅ b : _]) :
  [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel]].
Proof.
  eapply (Split_bind (hB _ _ _ ohA _ _ hab)).
  intros Ξ wfΞ ρΞ ohab.
  eapply (Split_wk_bind_return (hB _ _ _ ohA _ _ (urefl hab)) ρΞ).
  intros Θ wfΘ ρΘ ohbb.
  etransitivity.
  + eapply hB, overtree_PSh, ohab; tea.
  + symmetry; now unshelve eapply hB, ohbb.
Qed. *)


Lemma kripkeLRurefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B'⟨wk_up A' ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]].
Proof.
  eapply kripkeLRlrefl.
  2: eapply SirrLRSym, hab.
  clear Δ a b ρ wfΔ hab.
  intros Δ a b ρ wfΔ hab.
  eapply SirrLR, SsymLR, SirrLR in hab.
  specialize (hB Δ b a ρ wfΔ hab).
  eapply Split_hom_PSh.
  2: apply hB.
  intros Ξ wfΞ ρΞ hB'.
  symmetry.
  now eapply hB'.
  Unshelve.
  3: symmetry; eapply hA.
  2: intros; symmetry; eapply hA.
  all: tea.
Qed.
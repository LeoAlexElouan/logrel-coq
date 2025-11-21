From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry.
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

  Record trans {Γ l1 l2 A B C}
   {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
   {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
  := {
    transRed : [LogRel@{i j k l} l1 | Γ ||- A ≅ C] ;
    transRedTm : forall t u v,
      [_ ||-<l1> t ≅ u : _ | RAB] ->
      [_ ||-<l2> u ≅ v : _ | RBC] ->
      [_ ||-<l1> t ≅ v : _ | transRed ]
  }.

  Arguments trans {_ _ _ _ _ _}.

  Section ConducheHelper.
    Context {Γ l1 l2 A B C}
      {RAB : [LogRel@{i j k l} l1 | Γ ||- A ≅ B]}
      {RBC : [LogRel@{i' j' k' l'} l2 | Γ ||- B ≅ C]}
      (RAC : trans RAB RBC)
      {a b} (hab : [Γ ||-<l1> a ≅ b : _ | RAC.(transRed)]).

      #[local]
      Lemma factor_right : [Γ ||-<l2> a ≅ b : _ | RBC].
      Proof.
        now eapply (symLR RBC).(symRedTm), irrLR, (symLR RAC.(transRed)).(symRedTm).
      Qed.

      #[local]
      Lemma factor_left : [Γ ||-<l1> a ≅ a : _ | RAB].
      Proof.
        eapply irrLR, RAC.(transRedTm).
        2: eapply irrLR, (symLR RAB).(symRedTm).
        all: now eapply irrLR.
      Qed.

      Definition factor : [Γ ||-<l1> a ≅ a : _ | RAB] × [Γ ||-<l2> a ≅ b : _ | RBC] :=
        (factor_left, factor_right).
  End ConducheHelper.



  Definition transPolyRed {Γ l1 l2 A1 B1 C1 A2 B2 C2}
    (PAB : PolyRed@{i j k l} Γ l1 A1 B1 A2 B2)
    (PBC : PolyRed@{i' j' k' l'} Γ l2 B1 C1 B2 C2)
    (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > B1⟨ρ⟩ ≅ C]),
      trans (PolyRed.shpRed PAB ρ h) RBC)
    (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
      (ha : [PolyRed.shpRed PAB ρ h | Δ ||- a ≅ b: _]) l2 C,
      dover (PolyRed.posRed PAB ρ h ha) (fun Ξ ρ' hSplit => forall (RBC : [Ξ ||-< l2 > B2[b .: ρ >> tRel]⟨ρ'⟩ ≅ C⟨ρ'⟩]),
          trans hSplit RBC)) :
    PolyRed@{i j k l} Γ l1 A1 C1 A2 C2.
  Proof.
    unshelve econstructor.
    - intros; unshelve eapply transRed, ihdom.
      2: eapply PBC.(PolyRed.shpRed).
      all: tea.
    - cbn; intros ????? hab.
      pose proof (factor _ hab) as [haa hab'].
      pose proof (PBC.(PolyRed.posRed)) as hBC.
      specialize (hBC _ _ _ _ _ hab').
      eapply (Split_bind_over hBC).
      intros Ξ ρ' hoverBC.
      eapply (Split_wk_bind_over (PolyRed.posRed PAB ρ h haa) ρ').
      intros Θ ρ'' hoveraa.
      apply Split_return.
      intros Ω ρ'''.
      unshelve eapply transRed, ihcod.
      2: apply hBC.
      3: apply haa.
      now do 2 eapply overtree_PSh.
      now eapply overtree_PSh.
  Qed.


  Context {Γ : context} {l1 l2 : TypeLevel} {A B C : term}.

  Definition transLRne (neAB : [Γ ||-Sne A ≅ B]) (neBC : [Γ ||-Sne B ≅ C]) :
    neRedTy.tyL neBC = neRedTy.tyR neAB ->
    trans (LRne_ l1 neAB) (LRne_ l2 neBC).
  Proof.
    unshelve econstructor.
    + apply LRne_; destruct neAB, neBC;  unshelve econstructor.
      3,4: tea.
      cbn in *; subst; now etransitivity.
    + cbn; intros ??? rtu ruv.
      pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
      assert [Γ |- neRedTy.tyL neBC ≅ neRedTy.tyL neAB].
      1:{ symmetry; destruct neBC, neAB; cbn in *; subst;
        eapply convty_term, convtm_convneu; tea; constructor. }
      destruct rtu, ruv; cbn in *; subst.
      econstructor; cbn; [tea|..].
      * eapply redtmwf_conv; tea.
      * etransitivity; tea; now eapply convneu_conv.
  Qed.


  Section transΠ.
    Context (ΠAB : [Γ ||-Π<l1> A ≅ B]) (ΠBC : [Γ ||-Π<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (ParamRedTy.domR ΠAB)⟨ρ⟩ ≅ C]),
        trans (PolyRed.shpRed ΠAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΠAB ρ h | Δ ||- a ≅ b: _]) l2 C, dover (PolyRed.posRed ΠAB ρ h ha)
          (fun Ξ ρ' hSplit => forall (RBC : [Ξ ||-< l2 > (ParamRedTy.codR ΠAB)[b .: ρ >> tRel]⟨ρ'⟩ ≅ C⟨ρ'⟩]),
            trans hSplit RBC))
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
      destruct isfun as [???? eqbody|]; constructor; tea.
      intros *.
      eapply irrLR in ha as ha'.
      specialize (eqbody Δ a b ρ h ha').
      eapply dSplit_solve; [clear eqbody | apply eqbody].
      intros Ξ ρ' hover hover' eqbody; cbn in *.
      eapply irrLR, eqbody.
    Defined.

    #[local]
    Definition piRedTmRight {t} : PiRedTm ΠBC t -> PiRedTm transΠ t.
    Proof.
      intros [?? isfun]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΠ; symmetry; eapply ParamRedTy.eq.
      destruct isfun as [???? eqbody|]; constructor; tea.
      - etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      - intros ??? ρ h hab.
        cbn in *; destruct ΠAB as [domA domB' codA codB' redA redBl eqdomAB eqAB polyRedAB]; cbn in *; subst; cbn.
        unshelve epose proof (factor (ihdom _ ρ h _ _ (PolyRed.shpRed ΠBC ρ h)) _)
          as [haa hab'].
        3: eapply irrLR, hab.
        destruct ΠBC as [domB domC codB codC redBr redC eqdomBC eqBC polyRedBC]; cbn in *.
        eassert ([_ | Δ ||- a ≅ a : domB⟨ρ⟩ ≅ _]) as haa' by eapply irrLR, symLR, haa.
        specialize (eqbody Δ a b ρ h hab') as eqab; cbn in *.
        specialize (eqbody Δ a a ρ h haa') as eqaa; cbn in *.
        clear eqbody.
        unshelve eapply (dSplit_bind_over eqab).
        intros Ξ ρ' hoverab' hovereqab.
        unshelve eapply (dSplit_wk_bind_over eqaa ρ').
        intros Θ ρ'' hoveraa' hovereqaa.
        unshelve eapply (Split_wk_bind_over (PolyRed.posRed polyRedAB ρ h haa) (ρ'' ∘w ρ')).
        intros Ω ρ''' hoveraa; cbn in *.
        eapply Split_return.
        intros Φ ρ'''' hover.
        eapply irrLR; clear hover.
        eapply ihcod.
        eapply (symLR _).(symRedTm), irrLR.
        apply eqaa. all: cycle 1.
        apply eqab.
        Unshelve. all: cycle 3.
        apply haa.
        all: cbn in *.
        3,4: now do 3 apply overtree_PSh.
        2,3: now do 2 apply overtree_PSh.
        now apply overtree_PSh.
      - eapply convneu_conv; tea; cbn; rewrite eqΠ; symmetry; apply ParamRedTy.eq.
    Defined.

    Definition transLRΠ : trans (LRPi' ΠAB) (LRPi' ΠBC).
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
        3: eapply irrLR, hab.
        destruct ΠBC as [domB domC codB codC redBr redC eqdomBC eqBC polyRedBC]; cbn in *.
        specialize (appl Δ a a ρ h haa).
        specialize (appr Δ a b ρ h hab').
        unshelve eapply (dSplit_bind_over appl).
        intros Ξ ρΞ hoveraa hoverl.
        unshelve eapply (dSplit_wk_bind_over appr ρΞ).
        intros Θ ρΘ hoverab hoverr.
        apply Split_return.
        intros Ω ρΩ hover.
        eapply irrLR; clear hover.
        eapply ihcod.
        eapply appl. all: cycle 1.
        replace (PiRedTmEq.nf ru) with (PiRedTmEq.nf ru').
        apply appr.
        Unshelve. all: cbn in *.
        2,3: now do 2 apply overtree_PSh.
        all: now apply overtree_PSh.
    Qed.

  End transΠ.

  Section transΣ.
    Context (ΣAB : [Γ ||-Σ<l1> A ≅ B]) (ΣBC : [Γ ||-Σ<l2> B ≅ C])
      (ihdom : forall Δ (ρ : Δ ≤ Γ) (h : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (ParamRedTy.domR ΣAB)⟨ρ⟩ ≅ C]),
        trans (PolyRed.shpRed ΣAB ρ h) RBC)
      (ihcod : forall Δ a b (ρ : Δ ≤ Γ) (h : [|- Δ])
        (ha : [PolyRed.shpRed ΣAB ρ h | Δ ||- a ≅ b: _]) l2 C, dover (PolyRed.posRed ΣAB ρ h ha)
        (fun Ξ ρ' hSplit => forall RBC : [Ξ ||-< l2 > (ParamRedTy.codR ΣAB)[b .: ρ >> tRel]⟨ρ'⟩ ≅ C⟨ρ'⟩],
        trans hSplit RBC))
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
      - intros ; now unshelve eapply irrLR, rfst.
      - intros.
        specialize (rsnd Δ ρ h).
        eapply dSplit_solve; [clear rsnd| apply rsnd].
        intros Ξ ρΞ hoverAB hover rsnd.
        eapply irrLR; clear hover.
        eapply rsnd.
    Defined.

    #[local]
    Definition sigRedTmRight {t} : SigRedTm ΣBC t -> SigRedTm transΣ t.
    Proof.
      intros [?? ispair]; econstructor; cbn in *.
      1: eapply redtmwf_conv; tea; rewrite eqΣ; symmetry; eapply ParamRedTy.eq.
      destruct ispair as [???????? rfst rsnd|].
      2: constructor; eapply convneu_conv; tea; cbn; rewrite eqΣ; symmetry; apply ParamRedTy.eq.
      unshelve eapply PairLRPair; tea.
      1: intros; now unshelve now eapply (symLR _).(symRedTm), irrLR, (symLR _).(symRedTm).
      1: etransitivity; tea; cbn; rewrite eqdom; apply ParamRedTy.eqdom.
      etransitivity; tea; cbn; destruct ΣAB as [???????? PAB]; cbn in *; subst.
      + erewrite 2!eq_subst_scons.
        apply Rel_PSh_root.
        eapply (split_bind_alg convty_shf).
        2: eapply PAB.(PolyRed.posRed).
        2: unshelve eapply (symLR _).(symRedTm), irrLR, rfst; gtyping.
        intros Δ ρ; eapply escapeEq.
      + intros; cbn in *.
        specialize (rsnd Δ ρ h).
        eapply dSplit_solve; [clear rsnd| apply rsnd].
        intros Ξ ρΞ hoverAB hover rsnd.
        eapply symLR, irrLR, symLR; clear hover.
        eapply rsnd.
      Unshelve.
      gtyping.
    Defined.

    Definition transLRΣ : trans (LRSig' ΣAB) (LRSig' ΣBC).
    Proof.
      exists (LRSig' transΣ); intros ??? [rt ru eqtu fsttu sndtu] [ru' rv equv fstuv snduv].
      pose proof (equ := whredtm_det (whredtm ru) (whredtm ru')); cbn in equ.
      unshelve econstructor.
      - now eapply sigRedTmLeft.
      - now eapply sigRedTmRight.
      - intros.
        cbn in *; destruct ΣAB; cbn in *; subst; cbn.
        unshelve (eapply irrLR, ihdom; [eapply fsttu|]).
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
        eapply (dSplit_bind_over sndtu).
        intros Ξ ρΞ hoverfsttu hoversndtu.
        eapply (dSplit_wk_bind_over snduv ρΞ).
        intros Θ ρΘ hoverfstuv hoversnduv.
        eapply (Split_wk_bind_return_over (PolyRed.posRed polyRedAB ρ h fsttu') (ρΘ∘w ρΞ)).
        intros Ω ρΩ hoverfsttu' hover; cbn in *.
        eapply irrLR; clear hover.
        eapply ihcod.
        eapply irrLR.
        eapply sndtu. all:cycle 1.
        replace (SigRedTmEq.nf ru) with (SigRedTmEq.nf ru').
        eapply snduv. Unshelve. all: cbn in *.
        4: eapply fsttu'.
        2,4: now do 2 eapply overtree_PSh.
        1,3: now eapply overtree_PSh.
        tea.
    Qed.

  End transΣ.

  Section transId.
  Context (IAB : [Γ ||-SId<l1> A ≅ B]) (IBC : [Γ ||-SId<l2> B ≅ C])
    (ihty: forall l2 C (RBC : [Γ ||-< l2 > IdRedTy.tyR IAB ≅ C]), trans (IdRedTy.tyRed IAB) RBC)
    (* (ihkr: forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) l2 C (RBC : [Δ ||-< l2 > (IdRedTy.tyR IAB)⟨ρ⟩ ≅ C]),
      trans (IdRedTy.tyKripke IAB ρ wfΔ) RBC) *)
    ( eqty: IdRedTy.tyL IBC = IdRedTy.tyR IAB )
    ( eqlhs: IdRedTy.lhsL IBC = IdRedTy.lhsR IAB )
    ( eqrhs: IdRedTy.rhsL IBC = IdRedTy.rhsR IAB ).

  Arguments IdRedTy.outTy _ /.

  Let eqId : IdRedTy.outTy IBC = tId (IdRedTy.tyR IAB) (IdRedTy.lhsR IAB) (IdRedTy.rhsR IAB).
  Proof. cbn; now rewrite eqty, eqlhs, eqrhs. Qed.

  Definition transId : [Γ ||-SId<l1> A ≅ C].
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
      + intros ?? ?%(irrLR tyRed) ; eapply (irrLR _ tyRed); now symmetry.
      + intros ??? ?%(irrLR tyRed) ?%(irrLR tyRed); eapply (irrLR _ tyRed); now etransitivity.
  Defined.

  Definition transIdPropEq {t u v} : IdPropEq IAB t u -> IdPropEq IBC u v -> IdPropEq transId t v.
  Proof.
    intros [|?? [?? conv]].
    - intros ruv; inversion ruv as [| ?? [?? whr%convneu_whne] ]; subst.
      2: inversion whr.
      constructor; cbn in *; destruct IAB as [????? rhsR], IBC ; cbn in *; subst; tea.
      2,4: now eapply irrLR.
      + etransitivity; [|tea]; now eapply escapeEq.
      + eapply ihty; [|tea]; tea.
      + unshelve eapply ihty. 1: exact rhsR. all: tea.
    - intros ruv; inversion ruv as [|?? []]; subst.
      1: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      constructor; cbn in *; destruct IAB, IBC; cbn in *; subst; tea.
      constructor; tea.
      1: now eapply ty_conv.
      etransitivity; tea; now eapply convneu_conv.
  Qed.

  Definition transIdRedTmEq {t u v} : [Γ ||-SId<l1> t ≅ u : _ | IAB] -> [Γ ||-SId<l2> u ≅ v : _ | IBC] -> [Γ ||-SId<l1> t ≅ v : _ | transId].
  Proof.
    intros rtu ruv; pose proof (whredtm_det (whredtmR rtu) (whredtmL ruv)).
    destruct rtu, ruv; cbn in *; subst; econstructor.
    + tea.
    + eapply redtmwf_conv; tea; rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + etransitivity; tea; eapply convtm_conv; tea.
      rewrite eqId; symmetry; apply IAB.(IdRedTy.eq).
    + now eapply transIdPropEq.
  Qed.

  Definition transLRId : trans (LRId' IAB) (LRId' IBC).
  Proof. exists (LRId' transId). intros; now eapply transIdRedTmEq. Qed.

  End transId.

  End TransitivityLemmas.

  Arguments trans : clear implicits.
  Arguments trans {_ _ _ _ _ _}.

  Lemma transNatRedTmEq {Γ} :
    (forall t u, SNatRedTmEq Γ t u -> forall v, SNatRedTmEq Γ u v -> SNatRedTmEq Γ t v) ×
    (forall t u, NatRedTmEq Γ t u -> forall v, NatRedTmEq Γ u v -> NatRedTmEq Γ t v) ×
    (forall t u, NatPropEq Γ t u -> forall v, NatPropEq Γ u v -> NatPropEq Γ t v).
  Proof.
    apply NatRedEqInduction with
      (P:= fun Γ t u _ => forall v, SNatRedTmEq Γ u v -> SNatRedTmEq Γ t v)
      (P1:= fun Γ t u _ => forall v, NatRedTmEq Γ u v -> NatRedTmEq Γ t v)
      (P0:= fun Γ t u _ => forall v, NatPropEq Γ u v -> NatPropEq Γ t v).
    all: clear Γ.
    - intros * rL rR eq prop ih ? Ruv.
      set (Rtu := Build_SNatRedTmEq _ _ _ rL rR eq prop).
      pose proof (equ := whredtm_det (whredtmR Rtu) (whredtmL Ruv)); cbn in equ; subst.
      depelim Ruv; cbn in *; econstructor; tea.
      + etransitivity; tea.
      + now eapply ih.
    - intros ?? h; inversion h as [| | ?? [?? whz%convneu_whne]]; subst.
      1: constructor.
      inversion whz.
    - intros ???? ih ? h; inversion h as [| | ?? [?? whs%convneu_whne]]; subst.
      2: inversion whs.
      constructor; eauto.
    - intros ??? [?? conv] ? h; inversion h as [ | |??  []]; subst.
      1,2: symmetry in conv; eapply convneu_whne in conv; inversion conv.
      do 2 constructor; tea; now etransitivity.
    - intros ??? d htu ih v h.
      apply Nat_SplitSNat in h.
      apply SplitSNat_Nat.
      eapply (Split_bind_over h).
      intros Δ ρ hoverh.
      eexists (DTree_PSh Δ d).
      intros Ξ ρΞ hoverd'.
      eapply ih.
      now eapply over_DTree_PSh.
      eapply h.
      now eapply overtree_PSh.
  Qed.

  Lemma transBoolPropEq {Γ} :
    forall t u, BoolPropEq Γ t u -> forall v, BoolPropEq Γ u v -> BoolPropEq Γ t v.
  Proof.
    intros ?? [ | | ?? [?? conv]].
    1,2: easy.
    intros ? h; inversion h as [| | ?? []]; subst.
    1,2: symmetry in conv; eapply convneu_whne in conv; inversion conv.
    do 2 constructor; tea; now etransitivity.
  Qed.

  Lemma transBoolRedTmEq {Γ} :
    forall t u, SBoolRedTmEq Γ t u -> forall v, SBoolRedTmEq Γ u v -> SBoolRedTmEq Γ t v.
  Proof.
    intros ?? hL ? hR.
    pose proof (equ := whredtm_det (whredtmR hL) (whredtmL hR)); cbn in equ.
    destruct hL, hR; subst.
    econstructor; tea.
    - now etransitivity.
    - now eapply transBoolPropEq.
  Qed.


  Definition transLRU@{h i j k l h' i' j' k' l' v} {l1}
    (ih : forall l', l' << l1 ->
      forall Γ l2 A B C (RAB : [Γ ||-<l'> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]),
        trans@{h i j k h' i' j' k' v} RAB RBC)
    {Γ l2 A B C}
    (h : [Γ ||-SU<l1> A ≅ B]) (h' : [Γ ||-SU<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} (LRU_ h) (LRU_ h').
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
      forall Γ l2 A B C (RAB : [Γ ||-<l'> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]),
        trans@{h i j k h' i' j' k' v} RAB RBC)
    Γ l2 A B C (RAB : [Γ ||-<l> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
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
        constructor; tea; subst; now etransitivity.
    - intros ΣAB ? ihdom ihcod ??? [ΣBC []]; cbn in *; subst; eapply transLRΣ; eauto.
      intros ???????? Ξ ρΞ hovera RBC. eapply ihdom. eapply ihcod.
    - intros IAB ihty ???? [IBC []]; cbn in *; subst.
      eapply transLRId; eauto.
  Qed.

  Theorem transLR0@{i j k l i' j' k' l' v}  {Γ l2 A B C} (RAB : [Γ ||-<zero> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    eapply transLR_rec; intros ? h; inversion h.
  Qed.

  Theorem transLR@{h i j k l h' i' j' k' l' v} {Γ l1 l2 A B C}
    (RAB : [Γ ||-<l1> A ≅ B]) (RBC : [Γ ||-<l2> B ≅ C]) :
    trans@{i j k l i' j' k' l' v} RAB RBC.
  Proof.
    destruct l1; [eapply transLR0| apply transLR_rec].
    intros ? h; inversion h; intros; eapply transLR0.
  Qed.

End Transitivity.

Instance perLRTy `{GenericTypingProperties} {Γ l} : PER (LRAdequate Γ (LogRel l)).
Proof.
  constructor.
  - intros A B RAB; exact (symLR RAB).(symRed).
  - intros A B C RAB RBC; exact (transLR RAB RBC).(transRed).
Defined.

Section Consequences.
Context `{GenericTypingProperties}.

Lemma lreflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ t : _ | RAB].
Proof. intros Rtu; eapply irrLR, (transLR RAB _).(transRedTm); tea; now eapply (symLR _).(symRedTm). Qed.

Lemma ureflRedTm  {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ u : _ | RAB].
Proof. intros Rtu%((symLR _).(symRedTm)); eapply (symLR _).(symRedTm); now eapply lreflRedTm. Qed.

Lemma symRedTm' {Γ l A B} {RAB : [Γ ||-<l> A ≅ B]} {t u} : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> u ≅ t : _ | RAB].
Proof.
  intros Rtu. eapply irrLR, (transLR RAB _).(transRedTm).
  2: now eapply (symLR _).(symRedTm).
  now eapply ureflRedTm.
Qed.

Lemma irrLRConv {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RA : [Γ ||-<l> A ≅ A']) (RB : [Γ ||-<l> B ≅ B']) {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(irrLR _ RAB)%((symLR _).(symRedTm))%symRedTm'; now eapply irrLR.
Qed.

Lemma irrLRCum@{i j k l i' j' k' l' i0 j0 k0 l0} {Γ l0 l l' A A' B B'}
  (RAB : [LogRel@{i0 j0 k0 l0} l0 | Γ ||- A ≅ B])
  (RA : [LogRel@{i j k l} l | Γ ||- A ≅ A'])
  (RB : [LogRel@{i' j' k' l'} l' | Γ ||- B ≅ B']) {t u} :
  [Γ ||-<l> t ≅ u : _ | RA ] -> [Γ ||-<l'> t ≅ u : _ | RB ].
Proof.
  intros Rtu%(irrLR _ RAB)%((symLR _).(symRedTm))%symRedTm'; now eapply irrLR.
Qed.


Lemma irrLRSym {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) (RBA : [Γ ||-<l> B ≅ A]) {t u} :
  [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RBA].
Proof. intros; now eapply irrLRConv. Qed.

Lemma irrLREq {Γ l A A' B B'} (RAB : [Γ ||-<l> A ≅ B]) (RAB' : [Γ ||-<l> A' ≅ B']) (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l> t ≅ u : _ | RAB'].
Proof. eapply irrLRConv; subst; now eapply lrefl. Qed.

Lemma irrLREqCum@{i j k l i' j' k' l'} {Γ l l' A A' B B'}
  (RAB : [LogRel@{i j k l} l | Γ ||- A ≅ B])
  (RAB' : [LogRel@{i' j' k' l'} l' | Γ ||- A' ≅ B'])
   (eqA : A = A') {t u}
  : [Γ ||-<l> t ≅ u : _ | RAB] -> [Γ ||-<l'> t ≅ u : _ | RAB'].
Proof. eapply irrLRCum; subst; now eapply lrefl. Qed.

End Consequences.

Instance perLRTm `{GenericTypingProperties} {Γ l A B} (RAB : [Γ ||-<l> A ≅ B]) :
  PER (RAB.(LRPack.eqTm)).
Proof.
  constructor.
  - intros ?? Rtu; now eapply symRedTm'.
  - intros ??? Rtu Ruv; eapply irrLR, (transLR _ _).(transRedTm); tea.
    now eapply irrLRConv.
    Unshelve. 2: now symmetry.
Qed.

Instance iperLRTm `{GenericTypingProperties} {Γ l} :
  IPER (LRAdequate Γ (LogRel l)) (fun _ => term) (fun _ _ RA => RA.(LRPack.eqTm)).
Proof.
  constructor.
  - intros; now eapply symLR.
  - intros; now eapply transLR.
Qed.

Lemma kripkeLRlrefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B[a .: ρ >> tRel] ≅ B[b .: ρ >> tRel]].
Proof.
  etransitivity; [eauto|].
  symmetry; now eapply hB, urefl.
Qed.

Lemma kripkeLRurefl `{GenericTypingProperties} {Γ l A A' B B'}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  [Δ a b] (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]) :
  [Δ ||-<l> B'[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]].
Proof.
  eapply kripkeLRlrefl; tea; intros; symmetry; eapply hB; now symmetry.
Qed.
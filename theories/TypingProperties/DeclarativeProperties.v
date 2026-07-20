(** * LogRel.TypingProperties.DeclarativeProperties: basic properties of declarative typing, showing it is an instance of generic typing. *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Stability by weakening *)


Section TypingWk.

  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) A t := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) A t u := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].


  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction.
    - trivial.
    - trivial.
    - trivial.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros ?????? ih ** ; rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
      all: rewrite wk_decl; eauto.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros Γ A i new wfΓ _ ht Iht hf Ihf Δ ρ hΔ.
      destruct (decide_in (list_at Δ (ren_index ρ i)) new) as [[] hin|hnotin].
      + specialize (Iht Δ (wk_new i new true ρ hin) hΔ).
        apply Iht.
      + specialize (Ihf Δ (wk_new i new false ρ hin) hΔ).
        apply Ihf.
      + set (new' := Build_newnat _ new hnotin).
        apply (wfTypeSplit (new := new')); tea.
        * pose (wk_Fup true ρ i new new' eq_refl).
          apply (Iht _ w).
          now constructor.
        * pose (wk_Fup false ρ i new new' eq_refl).
          apply (Ihf _ w).
          now constructor.
    - intros * _ IHΓ Hnth ? * ?.
      econstructor; tea.
(*       eapply typing_meta_conv.
      1: econstructor ; tea. *)
      eapply in_ctx_wk ; tea.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      econstructor.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ ρ).
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHf _ IHu ? ρ ?.
      specialize (IHf _ ρ H).
      specialize (IHu _ ρ H).
      rewrite <- wk_app; rewrite <- wk_decl, <- wk_prod in IHf.
      eapply typing_meta_conv.
      1: now econstructor.
      rewrite <- wk_decl; f_equal.
      apply subst_ren_wk_up.
    - intros; now constructor.
    - intros; now constructor.
    - intros ?? Hn IHn ?? wfΔ.
      rewrite wk_succ.
      constructor. now apply IHn.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite <- wk_natElim, <- wk_decl,  subst_ren_wk_up; eapply wfTermNatElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy'.
        now eapply ihhs.
      * now eapply ihn.
    - intros; now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros * ? ihP ? ihht ? ihhf ? ihn **.
      erewrite <- wk_decl, <- wk_boolElim, subst_ren_wk_up; eapply wfTermBoolElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * now eapply ihn.
    - intros.
      rewrite <- wk_alpha.
      rewrite <- (ren_index_to_ren ρ). now eapply wfTermAlpha.
    - intros; now constructor.
    - intros * ? ihP ? ihe **.
      erewrite <- wk_emptyElim, <- wk_decl, subst_ren_wk_up; eapply wfTermEmptyElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.
    - intros; now constructor.
    - intros ?? Hn IHn ?? wfΔ.
      change (tLeaf n)⟨ρ⟩ with (tLeaf n⟨ρ⟩).
      constructor. now eapply IHn.
    - intros ???? Hn IHn Htl IHtl Htr IHtr ?? wfΔ.
      change (tNode n tl tr)⟨ρ⟩ with (tNode n⟨ρ⟩ tl⟨ρ⟩ tr⟨ρ⟩).
      constructor.
      * now eapply IHn.
      * now eapply IHtl.
      * now eapply IHtr.
    - intros * ? ihP ? ihhl ? ihhn ? iht **.
      erewrite <- wk_treeElim, <- wk_decl, subst_ren_wk_up; eapply wfTermTreeElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * rewrite wk_elimLeafHypTy'.
        now eapply ihhl.
      * rewrite wk_elimNodeHypTy'.
        now eapply ihhn.
      * now eapply iht.
    - intros ???? ih1 ? ih2 ** ; rewrite <- wk_sig; cbn.
      constructor.
      1: now eapply ih1.
      eapply ih2 ; constructor; eauto.
      constructor. now eapply ih1.
    - intros ?????? ihA ? ihB ? iha ? ihb **.
      rewrite <- wk_decl, <- wk_sig, <- wk_pair.
      constructor; eauto.
      1: eapply ihB; constructor; eauto.
      1: eapply iha; eauto.
      rewrite <- subst_ren_wk_up.
      now eapply ihb.
    - intros ???? Hp IHp ?? wfΔ.
      rewrite <- wk_fst.
      econstructor; now eapply IHp.
    - intros ????? ih **.
      erewrite <- wk_decl, subst_ren_wk_up.
      econstructor.
      eapply typing_meta_conv.
      1: eapply ih; tea.
      now rewrite <- wk_decl, <- wk_sig.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id, <- wk_decl.
      constructor.
      + now eapply IHA.
      + now eapply IHx.
      + now eapply IHy.
    - intros * _ IHA _ IHx **; rewrite <- wk_decl, <- wk_Id, <- wk_refl.
      constructor; eauto.
      now eapply IHx.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- wk_decl, <- wk_idElim.
      erewrite subst_ren_wk_up2.
      assert [|- Δ ,, term_decl A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + now eapply IHx.
      + rewrite ! wk_decl, 2!(wk_up_wk1 ρ).
        eapply IHP. rewrite <- wk_decl; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1.
          now eapply IHx.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2.
        now eapply IHhr.
      + now eapply IHy.
      + now eapply IHe.
    - intros * wfΓ _ _ iht * wfΔ.
      rewrite <- wk_decl, <- wk_xi. constructor; eauto.
      eapply iht. constructor; tea.
    - intros * wfΓ _ _ iht _ ihu * wfΔ.
      erewrite <- wk_decl, <- wk_xxi, <-wk_Id, <- wk_dEval',
        <- wk_xi, <-wk_eval, subst_ren_wk_up. constructor; eauto.
      eapply iht. constructor;tea.
      now eapply ihu.
    - intros * _ iht * wfΔ.
      rewrite <- wk_decl, <- wk_arr',  <- wk_eval.
      constructor.
      now eapply iht.
    - intros * _ iht _ ihtconv * wfΔ.
      rewrite <- wk_box.
      constructor; eauto.
      + eapply iht; tea.
      + intros * inℓ.
        rewrite <- (wk_nat_to_term ρ), <- (wk_bool_to_term ρ).
        eapply ihtconv; tea.
    - intros * _ ihP _ ihht _ ihhf _ ihn _ ihb _ ihconv * wfΔ.
      erewrite <- wk_decl, <- wk_ellElim, subst_ren_wk_up.
      set (ℓt := cons_ell ℓ k true) in *.
      set (ℓf := cons_ell ℓ k false) in *.
      constructor; eauto; fold ℓt ℓf.
      + eapply ihP; constructor; tea.
      + eapply typing_meta_conv.
        eapply ihht.
        1: constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply typing_meta_conv.
        eapply ihhf.
        1: constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + now eapply ihn.
      + now eapply ihb.
      + rewrite <- (wk_nat_to_term ρ). eapply ihconv; tea.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros Γ t A i new wfΓ _ ht Iht hf Ihf Δ ρ hΔ.
      destruct (decide_in (list_at Δ (ren_index ρ i)) new) as [[] hin|hnotin].
      + specialize (Iht Δ (wk_new i new true ρ hin) hΔ).
        apply Iht.
      + specialize (Ihf Δ (wk_new i new false ρ hin) hΔ).
        apply Ihf.
      + set (new' := Build_newnat _ new hnotin).
        apply (wfTermSplit (new := new')); tea.
        * pose (wk_Fup true ρ i new new' eq_refl).
          apply (Iht _ w).
          now constructor.
        * pose (wk_Fup false ρ i new new' eq_refl).
          apply (Ihf _ w).
          now constructor.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros ?????????? ih **.
      do 2 rewrite <- wk_sig; constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2!wk_Id; constructor; eauto.
      + now eapply IHx.
      + now eapply IHy.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
    - intros Γ A B i new wfΓ _ ht Iht hf Ihf Δ ρ hΔ.
      destruct (decide_in (list_at Δ (ren_index ρ i)) new) as [[] hin|hnotin].
      + specialize (Iht Δ (wk_new i new true ρ hin) hΔ).
        apply Iht.
      + specialize (Ihf Δ (wk_new i new false ρ hin) hΔ).
        apply Ihf.
      + set (new' := Build_newnat _ new hnotin).
        apply (TypeSplit (new := new')); tea.
        * pose (wk_Fup true ρ i new new' eq_refl).
          apply (Iht _ w).
          now constructor.
        * pose (wk_Fup false ρ i new new' eq_refl).
          apply (Ihf _ w).
          now constructor.
    - intros Γ u t A B _ IHA _ IHt _ IHu ? ρ ?.
      eapply convtm_meta_conv.
      rewrite <- wk_app, <- wk_lam.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + eapply (f_equal term_decl), subst_ren_wk_up.
      + eapply subst_ren_wk_up.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea; now econstructor.
    - intros Γ u u' f f' A B _ IHf _ IHu ? ρ wfΔ.
      specialize (IHf Δ ρ wfΔ).
      specialize (IHu Δ ρ wfΔ).
      rewrite <-2 wk_app; rewrite <- wk_decl, <- wk_prod in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + eapply (f_equal term_decl), subst_ren_wk_up.
      + reflexivity.
    - intros * _ IHA _ IHA' _ IHA'' _ IHe ? ρ ?.
      cbn; econstructor; try easy.
      apply (IHe _ (wk_up _ ρ)).
      now constructor.
    - intros * _ IHf ? ρ ?.
      rewrite <- wk_lam, <- wk_app, <- wk_up_wk1.
      now apply TermFunEta, IHf.
    - intros * ? ih **; cbn; constructor; now apply ih.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite <- wk_decl, <- ! wk_natElim, subst_ren_wk_up.
      econstructor.
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihhz.
        2: reflexivity.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy'.
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihhz ? ihhs **.
      erewrite <- wk_natElim, <- wk_decl, subst_ren_wk_up.
      eapply TermNatElimZero; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy'.
        now eapply ihhs.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      rewrite <- 2wk_app, <- 2wk_natElim, <- wk_decl, (subst_ren_wk_up (A:= tNat)), wk_succ.
      eapply TermNatElimSucc; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy'.
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihht ? ihhf ? ihn **.
      erewrite <-! wk_boolElim, <- wk_decl, subst_ren_wk_up.
      eapply TermBoolElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihht.
        2: reflexivity.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * eapply convtm_meta_conv.
        1: now eapply ihhf.
        2: reflexivity.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * now eapply ihn.
    - intros * ? ihP ? ihht ? ihhf **.
      erewrite <- wk_boolElim, <- wk_decl, subst_ren_wk_up.
      eapply TermBoolElimTrue; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite <- wk_decl, subst_ren_wk_up.
    - intros * ? ihP ? ihht ? ihhf **.
      erewrite <- wk_boolElim, <- wk_decl, subst_ren_wk_up.
      eapply TermBoolElimFalse; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihht.
        now erewrite <- wk_decl, subst_ren_wk_up.
      * eapply typing_meta_conv.
        1: now eapply ihhf.
        now erewrite <- wk_decl, subst_ren_wk_up.
    - intros Γ i n b hΓ _ hin Δ ρ hΔ.
      rewrite <-wk_app, wk_nat_to_term, wk_bool_to_term.
      cbn. rewrite <- (ren_index_to_ren ρ). constructor; tea.
      now eapply well_Fwk_in.
    - intros * ? ihP ? ihe **.
      erewrite <-! wk_emptyElim, <- wk_decl, subst_ren_wk_up.
      eapply TermEmptyElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros ??? _ ihn * wfΔ.
      rewrite <- ! wk_leaf, <- wk_decl.
      constructor.
      now eapply ihn.
    - intros ??????? _ IHn _ IHtl _ IHtr ?? wfΔ.
      rewrite <- ! wk_node, <- wk_decl.
      constructor; eauto.
      + now eapply IHn.
      + now eapply IHtl.
      + now eapply IHtr.
    - intros * ? ihP ? ihhl ? ihhn ? iht **.
      erewrite <- 2wk_treeElim, <- wk_decl, subst_ren_wk_up.
      eapply TermTreeElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * rewrite wk_elimLeafHypTy'.
        now eapply ihhl.
      * rewrite wk_elimNodeHypTy'.
        now eapply ihhn.
      * now eapply iht.
    - intros * ? ihP ? ihn ? ihhl ? ihhn **.
      erewrite <- wk_app, <- wk_treeElim, <- wk_leaf, <- wk_decl, subst_ren_wk_up.
      eapply TermTreeElimLeaf.
      * eapply ihP; repeat constructor; tea.
      * now eapply ihn.
      * rewrite wk_elimLeafHypTy'.
        now eapply ihhl.
      * rewrite wk_elimNodeHypTy'.
        now eapply ihhn.
    - intros * ? ihP ? ihn ? ihhl ? ihhn ? ihtl ? ihtr **.
      erewrite <-! wk_app, <-! wk_treeElim, <- wk_decl, subst_ren_wk_up, <- wk_node.
      eapply TermTreeElimNode.
      * eapply ihP; repeat constructor; tea.
      * now eapply ihn.
      * rewrite wk_elimLeafHypTy'.
        now eapply ihhl.
      * rewrite wk_elimNodeHypTy'.
        now eapply ihhn.
      * now eapply ihtl.
      * now eapply ihtr.
    - intros * _ IHA _ IHAA' _ IHBB' ** .
      rewrite <-! wk_sig, <- wk_decl.
      constructor; eauto.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB'.
        rewrite <- wk_decl.
        constructor; tea.
        constructor.
        eapply IHA; tea.
    - intros * _ ihA₀ _ ihA _ ihA' _ ihB _ ihB' _ iha _ ihb * wfΔ.
      rewrite <- wk_decl, <- wk_sig, <-! wk_pair.
      assert [|-[de] Δ,, term_decl A⟨ρ⟩] by now constructor.
      constructor; eauto.
      { now eapply iha. }
      eapply convtm_meta_conv.
      1: eapply ihb; tea.
      2: reflexivity.
      now erewrite <- wk_decl, subst_ren_wk_up.
    - intros * ? ihp Δ ρ **.
      rewrite <- wk_decl, <- wk_sig, <- wk_pair.
      constructor; rewrite wk_sig.
      now eapply ihp.
    - intros * ? ih **. econstructor; now eapply ih.
    - intros * _ ihA _ ihB _ iha _ ihb * wfΔ ; rewrite <- wk_fst; rewrite <- wk_pair; constructor; eauto.
      1: eapply ihB; constructor; eauto.
      { now eapply iha. }
      rewrite <- subst_ren_wk_up.
      now eapply ihb.
    - intros * ? ih **.
      erewrite <-! wk_snd, <- wk_decl, subst_ren_wk_up, <- wk_fst.
      econstructor.
      eapply convtm_meta_conv.
      1: eapply ih; tea.
      2: reflexivity.
      now rewrite <- wk_decl, <- wk_sig.
    - intros * _ ihA _ ihB _ iha _ ihb * wfΔ.
      assert [|-[de] Δ,, term_decl A⟨ρ⟩] by now constructor.
      erewrite <- wk_decl, subst_ren_wk_up, <- wk_fst, <- wk_snd, <- wk_pair.
      econstructor; eauto.
      { now eapply iha. }
      eapply typing_meta_conv.
      eapply ihb; tea.
      now erewrite <- wk_decl, subst_ren_wk_up.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2! wk_Id; constructor.
      + now eapply IHA.
      + now eapply IHx.
      + now eapply IHy.
    - intros * _ IHA _ IHx **.
      rewrite <- wk_decl, <-! wk_refl, <- wk_Id.
      constructor; eauto.
      now eapply IHx.
    - intros * _ IHA0 _ IHx0 _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      erewrite <- 2!wk_idElim, <- wk_decl, subst_ren_wk_up2.
      assert (wfΔA : [|- Δ ,, term_decl A⟨ρ⟩]) by (constructor; eauto).
      constructor; eauto.
      + now eapply IHx0.
      + now eapply IHx.
      + rewrite wk_decl, 2!(wk_up_wk1 ρ).
        eapply IHP.
        rewrite <- wk_decl. constructor; tea.
        rewrite <- wk_Id. constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1.
          now eapply IHx0.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2.
        now eapply IHhr.
      + now eapply IHy.
      + now eapply IHe.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHA' _ IHz _ IHAA' _ IHxy _ IHxz **.
      erewrite <- wk_idElim, <- wk_decl, subst_ren_wk_up2, <- wk_refl.
      assert [|- Δ ,, term_decl A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + now eapply IHx.
      + rewrite wk_decl, 2!(wk_up_wk1 ρ).
        eapply IHP. rewrite <- wk_decl. constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1.
          now eapply IHx.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2.
        now eapply IHhr.
      + now eapply IHy.
      + now eapply IHz.
      + now eapply IHxy.
      + now eapply IHxz.
    - intros * wfΓ _ _ ihtt' * wfΔ.
      rewrite <- wk_decl, <-! wk_xi.
      eapply TermXiCong; tea.
      eapply ihtt'.
      constructor; tea.
    - intros * wfΓ _ * wfΔ.
      rewrite <- wk_decl, <- wk_xi, <- wk_leaf, ! wk_nat_to_term.
      now constructor.
    - intros * wfΓ _ _ iht net ene * wfΔ.
      erewrite <- wk_decl, <- wk_node, wk_nat_to_term, <-! wk_xi,
        ! subst_ren_wk_up, <-! up_wk_up_wk1.
      eapply TermXiNode; tea.
      + eapply iht.
        constructor; tea.
      + eapply (whne_ren_wl _ _ net).
      + now rewrite head_ren_wl, ene.
    - intros * wfΓ _ _ ihtt' _ ihuu' * wfΔ.
      erewrite <- wk_decl, <-! wk_xxi, <- wk_Id, <- wk_dEval', <-wk_xi,
        <- wk_eval, subst_ren_wk_up.
      eapply TermXXiCong; tea.
      + eapply ihtt'.
        constructor; tea.
      + eapply ihuu'; tea.
    - intros * wfΓ _ _ ihu * wfΔ*.
      erewrite <- wk_decl, <- wk_refl, <- wk_xxi, <- wk_Id, !wk_nat_to_term.
      eapply TermXXiLeaf; tea.
      eapply ihu; tea.
    - intros * nem ene hm ihm _ ihn * wfΔ.
      set (ℓt := cons_ell ℓ k true); set (ℓf := cons_ell ℓ k false).
      erewrite <- wk_decl, <- wk_ellElim, <-! wk_Id, <-! wk_dEval',
        <-! wk_xxi, ! subst_ren_wk_up, <-! wk_box,
        <-! wk_app, wk_nat_to_term, <-! wk_eval, <-! wk_xi, <-! up_wk_up_wk1.
      eapply convtm_meta_conv.
      eapply TermXXiNode.
      + eapply (whne_ren_wl _ _ nem).
      + now rewrite head_ren_wl, ene.
      + eapply ihm.
        constructor; tea.
      + eapply ihn; tea.
      + reflexivity.
      + fold ℓt ℓf.
        repeat f_equal.
        * eapply eq_sym, up_wk_up_wk1.
        * eapply eq_sym, up_wk_up_wk1.
        * eapply eq_sym, up_wk_up_wk1.
    - intros * _ ihtt' * wfΔ.
      rewrite <- wk_decl, <- wk_arr', <-! wk_eval.
      eapply TermEvalCong, ihtt'; tea.
    - intros * wfΓ _ inℓ * wfΔ.
      rewrite wk_bool_to_term, <- wk_app, wk_nat_to_term.
      now constructor.
    - intros * _ iht _ ihconv * wfΔ.
      rewrite <- wk_decl, <- wk_arr', <- wk_eval, <- wk_box.
      eapply TermEvalBox.
      + eapply iht; tea.
      + intros * inℓ.
        rewrite <- (wk_nat_to_term ρ), <- (wk_bool_to_term ρ).
        eapply ihconv; tea.
    - intros * _ ihtt' _ ihconv * wfΔ.
      rewrite <-! wk_box.
      eapply TermBoxCong.
      + eapply convtm_meta_conv.
        1: eapply ihtt'; tea.
        2: reflexivity.
        now rewrite <- wk_decl, <- wk_arr'.
      + intros * inℓ.
        rewrite <- (wk_nat_to_term ρ), <- (wk_bool_to_term ρ).
        eapply ihconv; tea.
    - intros * _ iht * wfΔ.
      rewrite <- wk_box, <- wk_eval.
      now econstructor; eapply iht.
    - intros * _ ihP _ ihht _ ihhf _ ihn _ ihb _ ihconv * wfΔ.
      erewrite <- wk_decl, subst_ren_wk_up, <-! wk_ellElim.
      eapply TermEllElimCong.
      + eapply ihP.
        constructor; tea.
      + eapply convtm_meta_conv.
        1: eapply ihht; constructor; tea.
        2: reflexivity.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply convtm_meta_conv.
        1: eapply ihhf; constructor; tea.
        2: reflexivity.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply ihn; tea.
      + eapply ihb; tea.
      + rewrite <- (wk_nat_to_term ρ).
        eapply ihconv; tea.
    - intros * _ ihP _ ihht _ ihhf _ ihn _ ihconv * wfΔ.
      erewrite <- wk_decl, ! subst_ren_wk_up, <- wk_ellElim.
      eapply TermEllElimTrue.
      + eapply ihP.
        constructor; tea.
      + eapply typing_meta_conv.
        1: eapply ihht; constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply typing_meta_conv.
        1: eapply ihhf; constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply ihn; tea.
      + rewrite <- (wk_nat_to_term ρ).
        eapply ihconv; tea.
    - intros * _ ihP _ ihht _ ihhf _ ihn _ ihconv * wfΔ.
      erewrite <- wk_decl, ! subst_ren_wk_up, <- wk_ellElim.
      eapply TermEllElimFalse.
      + eapply ihP.
        constructor; tea.
      + eapply typing_meta_conv.
        1: eapply ihht; constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply typing_meta_conv.
        1: eapply ihhf; constructor; tea.
        now erewrite <- wk_decl, subst_ren_wk_up, <- up_wk_up_wk1.
      + eapply ihn; tea.
      + rewrite <- (wk_nat_to_term ρ).
        eapply ihconv; tea.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?. rewrite <- wk_decl.
      econstructor.
      + now eapply IHt.
      + now eapply IHA.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
    - intros Γ t t' A i new wfΓ _ ht Iht hf Ihf Δ ρ hΔ.
      destruct (decide_in (list_at Δ (ren_index ρ i)) new) as [[] hin|hnotin].
      + specialize (Iht Δ (wk_new i new true ρ hin) hΔ).
        apply Iht.
      + specialize (Ihf Δ (wk_new i new false ρ hin) hΔ).
        apply Ihf.
      + set (new' := Build_newnat _ new hnotin).
        apply (TermSplit (new := new')); tea.
        * pose (wk_Fup true ρ i new new' eq_refl).
          apply (Iht _ w).
          now constructor.
        * pose (wk_Fup false ρ i new new' eq_refl).
          apply (Ihf _ w).
          now constructor.
Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⤳* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Definition boundary_ctx_ctx {Γ A} : [|- Γ,, A] -> [|- Γ].
  Proof.
    intros.
    remember (Γ,,A) as ΓA eqn:eΓA.
    induction H in Γ, A, eΓA|-*.
    - inversion eΓA.
    - destruct Γ0 as [Γ' L'], Γ as [Γ L]; cbn in *.
      inversion eΓA; subst.
      change [|- ?G ] with [|- (Build_context Γ L'),, i : new ↦ b].
      eapply connew, IHWfContextDecl, eq_refl.
    - destruct Γ0 as [[|A' Γ'] L'], Γ as [Γ L]; cbn in *.
      + inversion eΓA.
      + inversion eΓA; subst.
        eapply (conalpha (Γ:=Build_context Γ' L')), IHWfContextDecl, eq_refl.
    - now induction eΓA using cons_eq_inversion.
    - now induction eΓA using cons_eq_inversion.
  Qed.

  Definition boundary_ctx_tip {Γ A} : [|- Γ,, term_decl A] -> [Γ |- A].
  Proof.
    intros.
    remember (Γ,,A) as ΓA eqn:eΓA.
    induction H in Γ, A, eΓA|-*.
    - inversion eΓA.
    - destruct Γ0 as [Γ' L'], Γ as [Γ L]; cbn in *.
      inversion eΓA; subst.
      destruct typing_wk as (_ & ? & _).
      rewrite <- (wk_id_ren_on (Build_context Γ L')),
        <- (wk_Fstep_ren_on (Γ:=(Build_context Γ L')) i new b).
      eapply w.
      + now eapply IHWfContextDecl.
      + constructor. eapply boundary_ctx_ctx, H.
    - destruct Γ0 as [[|A' Γ'] L'], Γ as [Γ L]; cbn in *.
      1: inversion eΓA.
      inversion eΓA; subst; clear eΓA.
      destruct A'; cbn in H1; inversion H1; subst.
      destruct typing_wk as (_ & ? & _).
      rewrite <- (wk_id_ren_on (Build_context Γ' L') t),
        <- (wk_alphastep_ren_on (F:=nil_ell) (Γ:=(Build_context Γ' L'))).
      eapply w.
      + now eapply IHWfContextDecl.
      + constructor. eapply boundary_ctx_ctx, H.
    - destruct Γ as [Γ L], Γ0 as [Γ' L'].
      now inversion eΓA; subst.
    - inversion eΓA.
  Qed.

  Definition boundary_tm_ctx {Γ} {t A} :
      [ Γ |- t : A ] ->
      [ |- Γ ].
  Proof.
    induction 1; eauto using boundary_ctx_ctx.
  Qed.

  Definition boundary_ty_ctx {Γ} {A} :
      [ Γ |- A ] ->
      [ |- Γ ].
  Proof.
    induction 1; eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_tm_conv_ctx {Γ} {t u A} :
      [ Γ |- t ≅ u : A ] ->
      [ |- Γ ].
  Proof.
      induction 1 ; eauto using boundary_tm_ctx, boundary_ty_ctx.
  Qed.

  Definition boundary_ty_conv_ctx {Γ} {A B} :
      [ Γ |- A ≅ B ] ->
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ty_ctx, boundary_tm_conv_ctx.
  Qed.


  Definition boundary_red_l {Γ t u K} :
    [ Γ |- t ⤳* u ∈ K] ->
    match K with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end.
  Proof.
    destruct 1; assumption.
  Qed.

  Definition boundary_red_tm_l {Γ t u A} :
    [ Γ |- t ⤳* u : A] ->
    [ Γ |- t : A ].
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {Γ A B} :
    [ Γ |- A ⤳* B ] ->
    [ Γ |- A ].
  Proof.
    apply @boundary_red_l with (K := istype).
  Qed.

End Boundaries.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_red_tm_l
  boundary_red_ty_l : boundary.


(** ** Typed reduction implies untyped reduction *)

Section TypeErasure.
  Import DeclarativeTypingData.

Lemma redtmdecl_red Γ t u A :
  [Γ |- t ⤳* u : A] ->
  [Γ | t ⤳* u].
Proof.
apply reddecl_red.
Qed.

Lemma redtydecl_red Γ A B :
  [Γ |- A ⤳* B] ->
  [Γ|A ⤳* B].
Proof.
apply reddecl_red.
Qed.

End TypeErasure.

(** ** Inclusion of the various reductions in conversion *)

Definition RedConvC {Γ} {t u : term} {K} :
    [Γ |- t ⤳* u ∈ K] ->
    match K with istype => [Γ |- t ≅ u] | isterm A => [Γ |- t ≅ u : A] end.
Proof.
apply reddecl_conv.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⤳* u : A] ->
    [Γ |- t ≅ u : A].
Proof.
apply @RedConvC with (K := isterm A).
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⤳* B] ->
    [Γ |- A ≅ B].
Proof.
apply @RedConvC with (K := istype).
Qed.

(** ** Weakenings of reduction *)

Lemma redtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⤳* u : A] -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros * ? []; split.
  - rewrite wk_decl. now apply typing_wk.
  - now apply credalg_Fwk.
  - rewrite wk_decl. now apply typing_wk.
Qed.

Lemma redtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⤳* B] -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩].
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - now apply credalg_Fwk.
  - now apply typing_wk.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app Γ A B f f' t :
  [ Γ |- f ⤳* f' : tProd A B ] ->
  [ Γ |- t : A ] ->
  [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ].
Proof.
  intros [] ?; split.
  + now econstructor.
  + now apply redalg_app.
  + econstructor; [tea|now apply TermRefl].
Qed.

Lemma redtmdecl_conv Γ t u A A' :
  [Γ |- t ⤳* u : A] ->
  [Γ |- A ≅ A'] ->
  [Γ |- t ⤳* u : A'].
Proof.
  intros [] ?; split.
  + now econstructor.
  + assumption.
  + now econstructor.
Qed.

Lemma redtydecl_term Γ A B :
  [ Γ |- A ⤳* B : U] -> [Γ |- A ⤳* B ].
Proof.
  intros []; split.
  + now constructor.
  + assumption.
  + now constructor.
Qed.

#[export] Instance RedTermTrans Γ A : Transitive (red_tm Γ A).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TermTrans.
Qed.

#[export] Instance RedTypeTrans Γ : Transitive (red_ty Γ).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TypeTrans.
Qed.

(** ** Bundling the properties together in an instance *)

Module WeakDeclarativeTypingProperties.
  Export DeclarativeTypingData.

  Import WeakDeclarativeTypingData.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-5: now constructor.
    1-6: boundary.
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  Lemma TermnSuccCong {Γ : context} {t u : term} {n : nat}:
    [Γ |-[ de ] t ≅ u : tNat] ->
    [Γ |-[ de ] nSucc n t ≅ nSucc n u : tNat].
  Proof.
    induction n; intros; tea; now econstructor.
  Defined.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - intros.
    econstructor; [|tea].
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros * ? H; apply H.
  - intros.
    now do 2 econstructor.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - intros.
    eapply TermTrans; [|now eapply TermFunEta].
    eapply TermTrans; [now eapply TermSym, TermFunEta|].
    constructor; tea.
    all: now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - now econstructor.
  - intros.
    eapply TermTrans; [|now constructor].
    eapply TermTrans; [eapply TermSym; now constructor|].
    constructor; tea; now apply TypeRefl.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  - intros * dt wft dt' wft' deta.
    eapply TermTrans; [|now constructor].
    eapply TermTrans; [eapply TermSym; now constructor|].
    constructor; tea.
    intros * inℓ.
    destruct wft.
    + eapply TermTrans, c; tea.
      eapply @TermAppCong with (B:=tBool); tea.
      constructor; tea.
      eapply TermnSuccCong, TermRefl, wfTermZero, boundary_tm_ctx; tea.
    + constructor; tea.
      boundary.
  Qed.


  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split; red.
    + intros ?? []; split; tea; now econstructor.
    + intros ??? [] []; split; tea; now econstructor.
  - intros ????? [] ?; split; tea; now econstructor.
  - intros ??????? []; split.
    + now eapply whne_ren.
    + now eapply whne_ren.
    + now eapply typing_wk.
  - now intros ???? [].
  - intros ????; split; now econstructor.
  - intros ?????; split.
    + constructor. eapply k.
    + constructor. eapply k.
    + change tBool with tBool[(nat_to_term k)..].
      eapply TermAppCong, TermnSuccCong, TermRefl, wfTermZero, boundary_tm_ctx, H.
      now eapply TermEvalCong, TermRefl.
  - intros ??????? [] ?; split; now econstructor.
  - intros ???????????? []; split; now econstructor.
  - intros ???????????? []; split; now econstructor.
  - intros ????? []; split.
    1-2 : now econstructor.
    eapply TermAppArrCong, TermnSuccCong; tea.
    do 2 constructor. boundary.
  - intros ?????? []; split; now econstructor.
  - intros ???????????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros * ??????? []; split; now econstructor.
  - intros * ?? []; split.
    1,2: now econstructor.
    eapply @TermAppCong with (B:=tBool), TermnSuccCong; tea.
    eapply TermEvalCong, TermRefl, wfVar; tea.
  - intros ??????? [] []; split; tea.
    now eapply TermSplit.
  - intros ?????? [nel ner hmm'] ene; split; tea.
    + eapply whne_tXi; tea.
    + eapply whne_tXi; tea.
    + eapply TermXiCong, TermnSuccCong, hmm'.
      eapply boundary_ctx_ctx, boundary_tm_conv_ctx, hmm'.
  - intros ????????? [nel ner hmm']; split; tea.
    + eapply whne_tXXi; tea.
    + eapply whne_tXXi; tea.
    + eapply TermXXiCong; tea.
      { eapply boundary_tm_conv_ctx; tea. }
      eapply TermnSuccCong, hmm'.
  - intros ????????????????????[]; split; tea.
    + now constructor.
    + now constructor.
    + eapply TermEllElimCong; tea.
  Qed.

  Lemma wfTermnSucc {Γ : context} {t : term} {n : nat}:
    [Γ |-[ de ] t : tNat] ->
    [Γ |-[ de ] nSucc n t : tNat].
  Proof.
    induction n; intros; [easy| now constructor].
  Defined.

  Lemma wfTermnattoterm {Γ : context} {n : nat}:
    [|-Γ] -> [Γ |-[ de ] nat_to_term n : tNat].
  Proof.
    induction n; now constructor.
  Defined.

  Lemma TermdEval'Cong {Γ t t' u u'} : [ |- Γ] ->
    [Γ |-[ de ] u ≅ u' : arr' Γ tNat tBool] ->
    [Γ |-[ de ] t ≅ t' : tTree] ->
    [Γ |-[ de ] dEval' Γ t u ≅ dEval' Γ t' u'  : tNat ].
  Proof.
    intros wfΓ du dt.
    assert (wfΓN : [ |- Γ,,tNat])
      by (repeat constructor; tea).
    assert (wfΓT : [ |- Γ,,tTree])
      by (repeat constructor; tea).
    assert (wfΓNT : [ |- Γ,, tNat,, tTree])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTT : [ |- Γ,, tNat,, tTree,, tTree])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTTN : [ |- Γ,, tNat,, tTree,, tTree,, tNat])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTTNN : [ |- Γ,, tNat,, tTree,, tTree,, tNat,, tNat])
      by (constructor; tea; constructor; tea). (* this makes the proof faster *)
    unfold dEval'.
    change (term_decl tNat) with (term_decl tNat[t..]).
    eapply TermTreeElimCong; tea.
    1-2: repeat (constructor; tea).
    constructor.
    1-3 : repeat (constructor; tea).
    cbn-[Tctx Fctx]; constructor.
    1-3 : repeat (constructor; tea).
    constructor.
    1-3 : repeat (constructor; tea).
    unfold elimNodeHypTyCod.
    cbn-[Tctx Fctx]; constructor.
    1-3 : repeat (constructor; tea).
    constructor.
    1-3 : repeat (constructor; tea).
    refine (TermBoolElimCong (P:=tNat) _ _ _ _).
    1-3 : repeat (constructor; tea).
    - eapply in_there with (A:=tNat), in_here.
    - eapply (TermAppCong (A:= tNat) (B:=tBool)).
      { repeat (eapply (convtm_wk (A:= tProd tNat tBool)); tea). }
      repeat (constructor; tea).
      do 4 eapply in_there with (A:= tNat).
      eapply in_here.
  Qed.

  Lemma wfTermdEvalNode {Γ u} : [ |- Γ] ->
    [Γ |-[ de ] u : arr' Γ tNat tBool] ->
    [Γ |-[ de ] dEvalNode' Γ u : elimNodeHypTy' Γ tNat ].
  Proof.
    intros wfΓ du.
    assert (wfΓN : [ |- Γ,,tNat])
      by (repeat constructor; tea).
    assert (wfΓNT : [ |- Γ,, tNat,, tTree])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTT : [ |- Γ,, tNat,, tTree,, tTree])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTTN : [ |- Γ,, tNat,, tTree,, tTree,, tNat])
      by (constructor; tea; constructor; tea).
    assert (wfΓNTTNN : [ |- Γ,, tNat,, tTree,, tTree,, tNat,, tNat])
      by (constructor; tea; constructor; tea). (* this makes the proof faster *)
    constructor.
    1 : repeat (constructor; tea).
    cbn-[Tctx Fctx]; constructor.
    1 : repeat (constructor; tea).
    constructor.
    1 : repeat (constructor; tea).
    unfold elimNodeHypTyCod.
    cbn-[Tctx Fctx]; constructor.
    1 : repeat (constructor; tea).
    constructor.
    1 : repeat (constructor; tea).
    eapply (wfTermBoolElim (P:=tNat)).
    1-3 : repeat (constructor; tea).
    - eapply in_there with (A:=tNat), in_here.
    - eapply (wfTermApp (A:= tNat) (B:=tBool)).
      { repeat (eapply (ty_wk (A:= tProd tNat tBool)); tea). }
      repeat (constructor; tea).
      do 4 eapply in_there with (A:= tNat).
      eapply in_here.
  Qed.
  Lemma wfTermdEval {Γ t u} : [ |- Γ] ->
    [Γ |-[ de ] u : arr' Γ tNat tBool] ->
    [Γ |-[ de ] t : tTree] ->
    [Γ |-[ de ] dEval' Γ t u : tNat ].
  Proof.
    intros wfΓ du dt.
    assert (wfΓT : [ |- Γ,,tTree])
      by (repeat constructor; tea). (* this makes the proof faster *)
    unfold dEval'.
    eapply (wfTermTreeElim (P:=tNat)); tea.
    1-2: repeat (constructor; tea).
    eapply wfTermdEvalNode;tea.
  Qed.

  Lemma TermdEval'Leaf {Γ n u} : [|-Γ] -> [Γ |- n : tNat] -> [Γ |- u : arr' Γ tNat tBool] ->
    [ Γ |- dEval' Γ (tLeaf n) u ≅ n : tNat ].
  Proof.
    intros wfΓ dn du.
    assert (wfΓN : [ |- Γ,,tNat])
      by (repeat constructor; tea).
    assert (wfΓT : [ |- Γ,,tTree])
      by (repeat constructor; tea).
    unfold dEval'.
    etransitivity.
    + eapply @TermTreeElimLeaf with (P:=tNat); tea.
      1,2 : repeat (constructor; tea).
      eapply wfTermdEvalNode;tea.
    + eapply @TermBRed with (B:=tNat) (t:= tRel 0); tea.
      all: repeat (constructor; tea).
  Qed.


  Lemma RedTermdEval'Leaf {Γ n u} : [|-Γ] -> [Γ |- n : tNat] -> [Γ |- u : arr' Γ tNat tBool] ->
    [ Γ |- dEval' Γ (tLeaf n) u ⤳* n : tNat ].
  Proof.
    intros wfΓ dn du; split.
    + eapply wfTermdEval; tea.
      eapply wfTermLeaf; tea.
    + unfold dEval'.
      econstructor; [eapply treeElimLeaf|].
      eapply redalg_one_step, @BRed with (t:=tRel 0).
    + eapply TermdEval'Leaf; tea.
  Qed.


(*    [Γ |-[ de ] dEval' Γ (tXi ℓ (nat_to_term n)) (tEval ℓ u) ≅ nat_to_term n : term_decl tNat] *)
  Lemma XXiLeafType {Γ ℓ u n} : [ |-[ de ] Γ] ->
    [Γ |-[ de ] u : ell_decl ℓ] ->
    [Γ |- tId tNat (dEval' Γ (tXi ℓ (nat_to_term n)) (tEval ℓ u)) (nat_to_term n)[u..] ≅
        tId tNat (nat_to_term n) (nat_to_term n) ].
  Proof.
    intros wfΓ du.
    assert (devu : [Γ |- tEval ℓ u : arr' Γ tNat tBool]) by (constructor; tea).
    econstructor.
    * now repeat constructor.
    * etransitivity.
      - eapply TermdEval'Cong; tea.
        1: eapply TermRefl; tea.
        eapply TermXiLeaf;tea.
      - eapply TermdEval'Leaf; tea.
        eapply wfTermnattoterm; tea.
    * rewrite <- nat_to_term_subst.
      eapply TermRefl, wfTermnattoterm;  tea.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - intros; now eapply redtmdecl_red.
  - intros. now eapply boundary_red_tm_l.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; now eapply redtmdecl_app.
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_boolElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * []; split.
    + eapply wfTermAppArr, wfTermnSucc; tea.
      constructor. boundary.
    + eauto using redalg_alpha.
    + eapply TermAppArrCong, TermnSuccCong; tea.
      do 2 constructor. boundary.
  - intros * ??; split.
    + eapply wfTermAppArr, wfTermnattoterm; tea.
      now constructor.
    + apply redalg_one_step. now econstructor.
    + now constructor.
  - intros * ? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_emptyElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_treeElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_fst.
    + now econstructor.
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_snd.
    + now econstructor.
  - intros **; split; refold.
    + econstructor; tea.
      econstructor.
      1: econstructor; tea; now econstructor.
      econstructor.
      1: now econstructor.
      1,2: econstructor; tea.
      1: now econstructor.
      eapply TermTrans; tea; now econstructor.
    + eapply redalg_one_step; constructor.
    + now econstructor.
  - intros * ????? []; split; refold.
    + now econstructor.
    + now eapply redalg_idElim.
    + econstructor; tea; now (eapply TypeRefl + eapply TermRefl).
  - intros; now eapply redtmdecl_conv.
  - intros; split.
    + assumption.
    + reflexivity.
    + now econstructor.
  - intros * ? []; split.
    + now eapply wfTermXi, wfTermnSucc.
    + now eapply redalg_xi.
    + now eapply TermXiCong, TermnSuccCong.
  - intros; split.
    + eapply wfTermXi, wfTermnattoterm; tea.
      now constructor.
    + eapply redalg_one_step; constructor.
    + now econstructor.
  - intros * ????; split.
    + now econstructor.
    + eapply redalg_one_step.
      do 2 replace t⟨wk_up _ _⟩ with t⟨upRen_term_term ↑⟩ by now bsimpl.
      eapply xiNode; tea.
    + now econstructor.
  - intros * ? [] ?; split.
    + eapply wfTermXXi; tea.
      eapply wfTermnSucc; tea.
    + now eapply redalg_xxi.
    + eapply TermXXiCong; tea.
      * eapply TermnSuccCong; tea.
      * eapply TermRefl; tea.
  - intros * wfΓ du; split.
    + eapply wfTermConv, XXiLeafType; tea.
      eapply wfTermXXi; tea.
      eapply wfTermnattoterm.
      constructor; tea.
    + eapply redalg_one_step.
      eapply xxiLeaf.
    + eapply TermTrans; [eapply TermXXiLeaf|];tea.
      * constructor; tea.
      * repeat (constructor; tea).
        eapply wfTermnattoterm; tea.
  - intros; split.
    + eapply wfTermXXi; tea.
      eapply boundary_tm_ctx; tea.
    + eapply redalg_one_step.
      repeat replace m⟨wk_up _ _⟩ with m⟨upRen_term_term ↑⟩ by now bsimpl.
      repeat replace m⟨upRen_term_term ↑⟩⟨wk_up _ _⟩ with m⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩ by now bsimpl.
      eapply xxiNode; tea.
    + now econstructor.
  - intros * []; split.
    + eapply (wfTermApp (A:=tNat) (B:=tBool)), wfTermnSucc; tea.
      do 2 constructor; tea. boundary.
    + eapply redalg_eval;tea.
    + eapply @TermAppCong with (A:=tNat) (B:=tBool), TermnSuccCong; tea.
      do 3 constructor;tea. boundary.
  - intros; split.
    + eapply (wfTermApp (A:=tNat) (B:=tBool)), wfTermnattoterm; tea.
      do 2 constructor; tea.
    + eapply redalg_one_step; constructor; tea.
    + now constructor.
  - intros; split.
    + constructor; constructor; tea.
    + eapply redalg_one_step.
      constructor.
    + constructor; tea.
  - intros * ???? [] ?; split.
    + constructor; tea.
    + eapply redalg_ellElim; tea.
    + constructor; tea.
      all: repeat (constructor; tea).
  - intros * ?????; split.
    + repeat (constructor; tea).
      boundary.
    + eapply redalg_one_step; constructor.
    + constructor; tea.
  - intros * ?????; split.
    + repeat (constructor; tea).
      boundary.
    + eapply redalg_one_step; constructor.
    + constructor; tea.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - intros; now eapply redtydecl_red.
  - intros. now eapply boundary_red_ty_l.
  - intros.
    now eapply redtydecl_term.
  - intros; split.
    + assumption.
    + reflexivity.
    + now constructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ := {}.

End WeakDeclarativeTypingProperties.
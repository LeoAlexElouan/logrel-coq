From Stdlib Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.
Set Primitive Projections.



Section Weakenings.
  Context `{GenericTypingProperties}.

  Record kripke@{i j k l} {Γ l A B} {RAB : [LogRel@{i j k l} l | Γ ||- A ≅ B]} := {
    wkRed : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [LogRel@{i j k l} l | Δ ||- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    wkRedTm : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) {t u},
      [Γ ||-S<l> t ≅ u : _ | RAB] -> [Δ ||-S<l> t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | wkRed ρ wfΔ] ;
  }.
  Arguments kripke {_ _ _ _} _.

  Definition wkStmt@{i j k l} l := (forall Γ A B (R : [LogRel@{i j k l} l | Γ ||- A ≅ B]), kripke R).

  Lemma wkU {Γ Δ l A B} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (h : [Γ ||-U<l> A ≅ B]) : [Δ ||-U<l> A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. destruct h; econstructor; tea; change U with U⟨ρ⟩; gen_typing. Defined.

  Lemma wkURedTerm {Γ Δ l t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    URedTm l Γ t -> URedTm l Δ t⟨ρ⟩.
  Proof.
    intros [te]. exists te⟨ρ⟩; change U with U⟨ρ⟩.
    - gen_typing.
    - apply isType_ren; assumption.
  Defined.

  Lemma wkLRU {l}
    (ih : forall l', l' << l -> wkStmt l')
    {Γ A B} {h : [Γ ||-U<l> A ≅ B]} : kripke (LRU_ h).
  Proof.
    unshelve econstructor.
    1: intros; now eapply LRU_, wkU.
    cbn; intros * [??? ?%redTyRecFwd]; unshelve econstructor.
    1,2: now eapply wkURedTerm.
    1: cbn; change (term_decl U) with (term_decl U)⟨ρ⟩; now eapply convtm_wk.
    eapply redTyRecBwd.
    eapply ih; cbn; tea.
    apply URedTy.lt.
  Qed.


  Lemma wkPoly {Γ l shp shp' pos pos' Δ}  (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    PolyRed Γ l shp shp' pos pos' ->
    PolyRed Δ l shp⟨ρ⟩ shp'⟨ρ⟩ pos⟨wk_up shp ρ⟩ pos'⟨wk_up shp' ρ⟩.
  Proof.
    intros []; opector.
    - intros ? ρ' ?; rewrite 2!wk_comp_ren_on; now eapply shpRed.
    - intros Ξ a b ρΞ wfΞ Hab.
      change (term_decl ?A⟨?ρ⟩) with (term_decl A)⟨ρ⟩.
      rewrite 2 wk_comp_ren_on, 2wk_up_wk_comp.
      unshelve eapply posRed; tea; eapply SirrLREq; tea; now rewrite wk_comp_ren_on.
  Qed.

  Lemma wkParamTy {T Γ A shp pos Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (wkT : forall (A B : term), (T A B : term)⟨ρ⟩ = T A⟨ρ⟩ B⟨wk_up A ρ⟩) :
    ParamRedTyPack.ParamTy (T:=T) Γ A shp pos -> ParamRedTyPack.ParamTy (T:=T) Δ A⟨ρ⟩ shp⟨ρ⟩ pos⟨wk_up shp ρ⟩.
  Proof.
    intros []; econstructor.
    1: rewrite <- wkT; gtyping.
    1: gtyping.
    eapply wft_wk; tea; gtyping.
  Qed.

  Lemma wkParamRedTy {T Γ l A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (wkT : forall A B : term, (T A B : term)⟨ρ⟩ = T A⟨ρ⟩ B⟨wk_up A ρ⟩) :
    ParamRedTy T Γ l A B -> ParamRedTy T Δ l A⟨ρ⟩ B⟨ρ⟩.
  Proof.
    intros []; econstructor.
    1,2: now eapply wkParamTy.
    1: gtyping.
    1: rewrite <- 2!wkT; gtyping.
    now eapply wkPoly.
  Defined.

  Lemma wkΠ  {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA : [Γ ||-Π< l > A ≅ B]) :
    [Δ ||-Π< l > A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. eapply wkParamRedTy; tea; intros; now rewrite wk_prod. Defined.

  Lemma wkΣ  {Γ Δ A B l} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΣA : [Γ ||-Σ< l > A ≅ B]) :
    [Δ ||-Σ< l > A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. eapply wkParamRedTy; tea; intros; now rewrite wk_sig. Defined.

  Lemma wk_isLRFun {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    isLRFun ΠA t -> isLRFun (wkΠ ρ wfΔ ΠA) t⟨ρ⟩.
  Proof.
    intros * [? A' t' wtdom convtydom Ht|i HΠ|ℓ v HΠ| ]; rewrite <-?wk_lam; constructor; tea; refold.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + intros Ξ a b ρΞ wfΞ *; cbn in *.
      eassert ([_ |_||- _≅ _ : term_decl (ParamRedTy.domL ΠA)⟨ρΞ∘w ρ⟩ ≅ _]) as ha'
        by (eapply SirrLREq; [eapply wk_comp_ren_on| eapply ha]).
      specialize (Ht _ _ _ (ρΞ∘w ρ) wfΞ ha').
      eapply (dSplit_bind_return Ht).
      intros Θ wfΘ ρΘ oha' oHt owk; cbn in *.
      change t'⟨wk_up A' ρ⟩ with t'⟨wk_up (ParamRedTy.domL ΠA) ρ⟩.
      replace t'⟨_⟩⟨_⟩ with t'⟨wk_up (ParamRedTy.domL ΠA) (ρΞ ∘w ρ)⟩
       by now rewrite <- wk_up_wk_comp, wk_comp_ren_on.
      unshelve eapply SirrLREq, Ht; tea.
      now rewrite <- wk_up_wk_comp, wk_comp_ren_on.
    + eapply (convty_wk _ wfΔ HΠ).
    + eapply (convty_wk _ wfΔ HΠ).
    + eapply (convneu_wk _ wfΔ c).
  Qed.

  Lemma wkPiRedTerm {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) (ΠA' := wkΠ ρ wfΔ ΠA) :
    PiRedTm ΠA t -> PiRedTm ΠA' t⟨ρ⟩.
  Proof.
    intros [nf].
    exists (nf⟨ρ⟩); cbn; try change (tProd _ _) with ((outTyL ΠA)⟨ρ⟩).
    + now eapply redtmwf_wk.
    + now apply wk_isLRFun.
  Defined.

  Lemma wkLRΠ {Γ l A B} (ΠA : [Γ ||-Π< l > A ≅ B]) : kripke (LRPi' ΠA).
  Proof.
    unshelve econstructor.
    - intros; now apply LRPi', wkΠ.
    - cbn ; intros * []; unshelve econstructor.
      1,2: now apply wkPiRedTerm.
      1: now eapply (convtm_wk _ wfΔ eq).
      intros Ξ a b ρΞ wfΞ hab. (* rewrite 2!wk_comp_ren_on. *)
      eassert ([_ |_||- _≅ _ : term_decl (ParamRedTy.domL ΠA)⟨ρΞ∘w ρ⟩ ≅ _]) as hab'
        by (eapply SirrLREq; [eapply wk_comp_ren_on| eapply hab]).
      specialize (eqApp Ξ a b (ρΞ∘w ρ) wfΞ hab').
      unshelve eapply (dSplit_bind_return eqApp); tea.
      intros Θ wfΘ ρΘ ohab' oeqApp owk.
      unfold wkPiRedTerm; cbn[PiRedTmEq.nf].
      rewrite 2wk_comp_ren_on.
      unshelve eapply SirrLREq, eqApp; tea.
      now rewrite <- wk_up_wk_comp, <- wk_comp_ren_on.
  Qed.

  Lemma wk_up_subst1 {Γ Δ F} t a (ρ : Γ ≤ Δ) : t⟨wk_up F ρ⟩[(a⟨ρ⟩)..] = t[a..]⟨ρ⟩.
  Proof. now bsimpl. Qed.

  Lemma wk_isLRPair {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    isLRPair ΣA t -> isLRPair (wkΣ ρ wfΔ ΣA) t⟨ρ⟩.
  Proof.
  intros * [A' B' a b wtydom convtydom wtycod convtycod Hfst Hsnd|];
    [change (tPair A' B' a b)⟨ρ⟩ with (tPair A'⟨ρ⟩ B'⟨wk_up A' ρ⟩ a⟨ρ⟩ b⟨ρ⟩)|]; unshelve econstructor; tea; refold.
  all: try first [now eapply wft_wk| now eapply convty_wk].
  + intros Ξ ρΞ wfΞ.
    rewrite wk_comp_ren_on; eapply SirrLREq; [|now unshelve eapply Hfst].
    cbn; now rewrite wk_comp_ren_on.
  + rewrite <- subst_ren_wk_up.
    now eapply wft_wk.
  + cbn-[ren1]. rewrite <- 2subst_ren_wk_up.
    now eapply convty_wk.
  + intros Ξ ρΞ wfΞ.
    specialize (Hsnd Ξ (ρΞ ∘w ρ) wfΞ).
    eapply (dSplit_bind_return Hsnd).
    intros Θ wfΘ ρΘ ofst osnd oirr.
    eapply SirrLREq; clear oirr.
    2:rewrite (wk_comp_ren_on b); now unshelve apply Hsnd.
    cbn. now rewrite 2wk_comp_ren_on.
  + cbn-[ren1]; rewrite wk_sig, wk_decl; now eapply convneu_wk.
  Qed.

  Lemma wkSigRedTerm {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) {t Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    SigRedTm ΣA t -> SigRedTm (wkΣ ρ wfΔ ΣA) t⟨ρ⟩.
  Proof.
    intros [nf].
    unshelve eexists (nf⟨ρ⟩); try (cbn-[ren1]; rewrite wk_sig).
    + now eapply redtmwf_wk.
    + apply wk_isLRPair; assumption.
  Defined.

  Lemma wkLRΣ {Γ l A B} (ΣA : [Γ ||-Σ< l > A ≅ B]) : kripke (LRSig' ΣA).
  Proof.
    unshelve econstructor.
    - intros; now apply LRSig', wkΣ.
    - cbn ; intros * []; unshelve econstructor.
      1,2: now apply wkSigRedTerm.
      2: cbn-[ren1]; rewrite wk_sig, wk_decl; now eapply convtm_wk.
      + intros Ξ ρ' wfΞ ; cbn; rewrite 2!wk_comp_ren_on.
        eapply SirrLREq; [now rewrite wk_comp_ren_on| now unshelve eapply eqFst].
      + intros Ξ ρΞ wfΞ ; cbn.
        specialize (eqSnd Ξ (ρΞ∘w ρ) wfΞ).
        eapply (dSplit_bind_return eqSnd).
        intros Θ wfΘ ρΘ oeqFst oeqSnd oirr; cbn in *.
        eapply SirrLREq; clear oirr.
        2: rewrite 2!wk_comp_ren_on; now unshelve eapply eqSnd.
        cbn; now rewrite 2wk_comp_ren_on.
  Qed.

  Lemma wkNat {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Nat A ≅ B] -> [Δ ||-Nat A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor.
    all: change tNat with tNat⟨ρ⟩; gtyping.
  Qed.

  Lemma wkBool {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Bool A ≅ B] -> [Δ ||-Bool A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor.
    all: change tBool with tBool⟨ρ⟩; gtyping.
  Qed.

  Lemma wkEmpty {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Empty A ≅ B] -> [Δ ||-Empty A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor; change tEmpty with tEmpty⟨ρ⟩; gtyping.
  Qed.

  Lemma wkTree {Γ A B Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) : [Γ ||-Tree A ≅ B] -> [Δ ||-Tree A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof.
    intros []; constructor.
    all: change tTree with tTree⟨ρ⟩; gtyping.
  Qed.

  Lemma wkId@{i j k l} {Γ l A B} (IA : IdRedTy@{i j k l} Γ l A B)
    (ih : kripke@{i j k l} IA.(IdRedTy.tyRed)) {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|- Δ]) :
    IdRedTy@{i j k l} Δ l A⟨ρ⟩ B⟨ρ⟩.
  Proof.
    unshelve econstructor.
    8,9: erewrite wk_Id; eapply redtywf_wk; tea; apply IA.(IdRedTy.redL) + apply IA.(IdRedTy.redR).
    2: rewrite 2!wk_Id; eapply convty_wk; tea; eapply IA.(IdRedTy.eq).
    - now eapply ih.(wkRed).
    - eapply wkRedTm; now destruct IA.
    - eapply wkRedTm; now destruct IA.
    - eapply SperLRTm.
  Defined.

  Lemma wkNeNfEq {Γ Δ k k' A} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    [Γ ||-NeNf k ≅ k' : A] -> [Δ ||-NeNf k⟨ρ⟩ ≅ k'⟨ρ⟩ : A⟨ρ⟩].
  Proof.
    intros []; constructor; gen_typing.
  Qed.

  Lemma wkNatTm Γ : (forall t u : term, [Γ ||-Nat t ≅ u:Nat] -> forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-Nat t⟨ρ⟩ ≅ u⟨ρ⟩:Nat])
    × (forall t u, NatPropEq Γ t u -> forall Δ (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] ->NatPropEq Δ t⟨ρ⟩ u⟨ρ⟩).
  Proof.
    apply NatRedEqInduction.
    * intros; econstructor; tea; change tNat with tNat⟨ρ⟩; rewrite ? wk_decl; try gtyping.
    * constructor.
    * now constructor.
    * intros; constructor.
      change (term_decl tNat) with (term_decl tNat)⟨ρ⟩.
      now eapply wkNeNfEq.
  Qed.

  Lemma wkBoolTm Γ t u : [Γ ||-Bool t ≅ u :Bool] ->
    forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-Bool t⟨ρ⟩ ≅ u⟨ρ⟩:Bool].
  Proof.
    intros [] ?? wfΔ.
    econstructor; change tBool with tBool⟨ρ⟩.
    1,2: now eapply redtmwf_wk.
    1: rewrite wk_decl; gtyping.
    destruct prop; constructor.
    change (term_decl tBool) with (term_decl tBool)⟨ρ⟩.
    now eapply wkNeNfEq.
  Qed.

  Lemma wkLR_rec@{h i j k l} {l} (ih : forall l', l' << l -> wkStmt@{h i j k} l') :
    wkStmt@{i j k l} l.
  Proof.
    intros Γ A B RAB; revert ih; indLR RAB.
    - intros; now apply wkLRU.
    - intros [] _; unshelve econstructor.
      + intros; apply LRne_; econstructor.
        1,2: now eapply redtywf_wk.
        change (term_decl ?A) with (term_decl A)⟨ρ⟩; gtyping.
      + cbn; intros * []; cbn in *; econstructor; cbn.
        1,2: now eapply redtmwf_wk.
        rewrite wk_decl.
        gtyping.
    - intros; eapply wkLRΠ.
    - intros; unshelve econstructor.
      + intros; now eapply LRNat_, wkNat.
      + cbn. intros ??? t u hNat; cbn in *.
        now eapply wkNatTm.
    - intros; unshelve econstructor.
      + intros; now apply LRBool_, wkBool.
      + cbn; intros ????? hBool.
        now eapply wkBoolTm.
    - intros; unshelve econstructor.
      + intros; now eapply LREmpty_, wkEmpty.
      + cbn; intros ????? []; econstructor; change tEmpty with tEmpty⟨ρ⟩.
        1,2: now eapply redtmwf_wk.
        rewrite wk_decl.
        now eapply wkNeNfEq.
    - intros; unshelve econstructor.
      + intros; now eapply LRTree_, wkTree.
      + intros ??? t u hTree; cbn-[ren1] in *.
        unfold TreeRedTmEq.
        induction hTree.
        * econstructor; tea; change tTree with tTree⟨ρ⟩; rewrite ? wk_decl.
          1,2:eapply redtmwf_wk; tea.
          eapply convtm_wk; tea.
        * cbn; constructor; now eapply wkNatTm.
        * cbn; constructor; tea; now eapply wkNatTm.
        * constructor.
        change (term_decl tTree) with (term_decl tTree)⟨ρ⟩.
        now eapply wkNeNfEq.
    - intros; eapply wkLRΣ.
    - intros IA ihty ih; unshelve econstructor.
      + intros ; eapply LRId', wkId; eauto.
      + intros * [????? prop]; econstructor; cbn-[ren1]; rewrite ?wk_Id.
        1,2: now eapply redtmwf_wk.
        1: rewrite wk_decl; now eapply convtm_wk.
        destruct prop; [rewrite <- 2wk_refl|]; constructor; cbn-[ren1]; rewrite ? wk_Id, ? wk_decl.
        1,2: now eapply wft_wk.
        1,2: now eapply ty_wk.
        1,2: now eapply convty_wk.
        5: now eapply wkNeNfEq.
        all: now eapply ihty.
  Qed.

  Theorem wkLR0@{i j k l} : wkStmt@{i j k l} zero.
  Proof.
    eapply wkLR_rec; intros ? h; inversion h.
  Qed.

  Theorem SwkLR@{h i j k l} {l}: wkStmt@{i j k l} l.
  Proof.
    intros; eapply wkLR_rec.
    intros ? h; inversion h. eapply wkLR0.
  Qed.


End Weakenings.

Section WeakWeakenings.
  Context `{GenericTypingProperties}.

  Record Wkripke@{i j k l} {Γ l A B} {RAB : WLRAdequate@{i j k l} Γ l A B} := {
    WwkRed : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), WLRAdequate@{i j k l} Δ l A⟨ρ⟩ B⟨ρ⟩;
    WwkRedTm : forall {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) {t u},
      [Γ ||-<l> t ≅ u : _ | RAB] -> [Δ ||-<l> t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | WwkRed ρ wfΔ] ;
  }.
  Arguments Wkripke {_ _ _ _} _.

  Definition WwkStmt@{i j k l} l := (forall Γ A B (R : WLRAdequate@{i j k l} Γ l A B), Wkripke R).

  Theorem wkLR@{h i j k l} {l}: WwkStmt@{i j k l} l.
  Proof.
    intros ????.
    unshelve econstructor.
    + intros ???.
      eapply (Split_wk_bind_return R wfΔ ρ).
      intros ????.
      rewrite 2wk_comp_ren_on.
      now eapply R.
    + intros ????? Rtu.
      eapply (dSplit_wk_bind_return Rtu wfΔ ρ).
      intros ??? oR oRtu oirr.
      eapply SirrLREq; clear oirr.
      symmetry; apply wk_comp_ren_on.
      rewrite 2!wk_comp_ren_on.
      now unshelve eapply Rtu.
  Qed.

  Lemma wkLRTy {Γ l A B Δ} (ρ : Δ ≤ Γ) (wfΔ:[|-Δ]) : [Γ ||-< l > A ≅ B] -> [Δ ||-< l > A⟨ρ⟩ ≅ B⟨ρ⟩].
  Proof. intros; now eapply wkLR. Qed.

  Lemma wkLRTm {Γ l A B Δ} (ρ : Δ ≤ Γ) (wfΔ:[|-Δ]) {RA : [Γ ||-< l > A ≅ B]} {t u} :
    [Γ ||-< l > t ≅ u : _ | RA] -> [Δ ||-< l > t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | wkLRTy ρ wfΔ RA].
  Proof. intros; now unshelve now eapply irrLR, wkLR. Qed.

End WeakWeakenings.


Lemma Wpackrefold `{GenericTypingProperties} :
  forall {Γ l t u A B Δ} wfΔ {ρ : Δ ≤ Γ} (RAB : [Γ ||-< l > A ≅ B])
    (RAB' := WwkRed (wkLR _ _ _ RAB) ρ wfΔ),
  [ Δ ||-< l > t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | RAB'] ->
  Split (fun (Ξ : context) wfΞ (ρΞ : Ξ ≤ Δ) =>
   forall oRAB,
   [cover RAB Ξ wfΞ (ρΞ ∘w ρ) oRAB | Ξ ||- t⟨ρΞ ∘w ρ⟩ ≅ u⟨
   ρΞ ∘w ρ⟩ : _ ≅ _]).
Proof.
  intros ??????????? Rtu.
  eapply (dSplit_bind_return Rtu).
  intros Ξ wfΞ ρΞ oRAB' oRtu oRAB.
  eapply SirrLREq. 1: apply wk_comp_ren_on.
  rewrite <- 2!wk_comp_ren_on.
  now unshelve eapply Rtu.
Qed.

Lemma WAd_return `{GenericTypingProperties} 
  {Γ} {l A B}
  (RAB : [Γ ||-S< l > A ≅ B]) : [Γ ||-< l > A ≅ B].
Proof.
  eapply Split_return; tea.
  1: escape; gtyping.
  intros ???.
  now eapply SwkLR.
Qed.

Lemma Wpack_return' `{GenericTypingProperties}
  {Γ} {l A B t u} {RAB : [Γ ||-S< l > A ≅ B]}  {RAB' : [Γ ||-< l > A ≅ B]}
  (Rtu : [Γ ||-S< l > t ≅ u : A | RAB] ) : [Γ ||-< l > t ≅ u : A |  RAB'].
Proof.
  eapply Split_return.
  1: escape; gtyping.
  intros ??? oRAB'.
  now unshelve eapply SirrLR, SwkLR, Rtu.
Qed.

Lemma Wpack_return `{GenericTypingProperties}
  {Γ l A B t u} {RAB : [Γ ||-S< l > A ≅ B]}
  (Rtu : [Γ ||-S< l > t ≅ u : A | RAB] ) : [Γ ||-< l > t ≅ u : A | WAd_return RAB].
Proof.
  unshelve eapply irrLR, Wpack_return', Rtu.
  now eapply WAd_return.
Qed.





From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application Nat Bool SimpleArr.

Section Ell.
  Context `{GenericTypingProperties}.

  Lemma SNtoBRed {Γ : context} (wfΓ : [|-Γ]) {l} : [Γ ||-S< l > arr' Γ tNat tBool ].
  Proof.
    eapply SArrRedTy.
    + intros. eapply SnatRed; tea.
    + intros. eapply SboolRed; tea.
  Qed.
  Lemma NtoBRed {Γ : context} (wfΓ : [|-Γ]) {l} : [Γ ||-< l > arr' Γ tNat tBool ].
  Proof. now eapply WAd_return, SNtoBRed. Qed.


  Lemma evalRelRedEqAux {ℓ : ell} {Γ l v} (wfΓ : [|-Γ]) : in_ctx Γ v ℓ -> (forall tL tR (Rt : [Γ ||-Nat tL ≅ tR :Nat]), forall k,
    [Γ ||-S< l > tApp (tEval ℓ (tRel v)) (nSucc k tL) ≅ tApp (tEval ℓ (tRel v)) (nSucc k tR) : _ | SboolRed wfΓ]) ×
    (forall tL tR (propt : NatPropEq Γ tL tR), forall k,
    [Γ ||-S< l > tApp (tEval ℓ (tRel v)) (nSucc k tL) ≅ tApp (tEval ℓ (tRel v)) (nSucc k tR) : _ | SboolRed wfΓ]).
  Proof.
    intros inv.
    apply NatRedEqInduction.
    + intros * [gL RL] [gR RR] nfeq nfprop ihnfprop ?.
      eapply SredSubstTmEq.
      { eapply (ihnfprop k). }
      1,2 : eapply redtm_eval; tea.
    + intros k.
      destruct (decide_in ℓ k).
      - eapply SredSubstTmEq.
        2,3: eapply redtm_evalRel; tea.
        destruct b.
        * eapply StrueRed.
        * eapply SfalseRed.
      - assert [Γ |- tApp (tEval ℓ (tRel v)) (nSucc k tZero) : tBool] as ty_evalRel.
         { eapply (ty_app (B:=tBool)), ty_nSucc, ty_zero; tea; eapply ty_eval, ty_var; tea. }
        eapply SneNfTermEq.
        constructor; tea.
        change k with (newnat_nat _ (Build_newnat _ k n)).
        eapply convneu_evalrel, ty_var; tea.
    + intros * Rnn' ihRnn' k.
      rewrite 2 nSuccswap.
      eapply ihRnn' with (k:=S k).
    + intros * [] k.
      eapply SneNfTermEq.
      constructor; tea.
      1,2 : eapply (ty_app (B:=tBool)), ty_nSucc; tea;
        eapply ty_eval, ty_var; tea.
      eapply convneu_eval; tea.
  Qed.

  Lemma SevalRelRedEq {ℓ : ell} {Γ l v t t' k} (wfΓ :[|-Γ]):  in_ctx Γ v ℓ -> [Γ ||-S< l > t ≅ t' : tNat | SnatRed (l:=l) wfΓ ] ->
    [ Γ ||-S< l > tApp (tEval ℓ (tRel v)) (nSucc k t) ≅ tApp (tEval ℓ (tRel v)) (nSucc k t') : tBool |SboolRed wfΓ].
  Proof.
    cbn.
    intros inv Rtt'.
    eapply (fst (evalRelRedEqAux wfΓ inv)); tea.
    Unshelve. tea.
  Qed.

  Lemma SirrEll {Γ l t t'} {ℓ : ell} (RNtoB RNtoB' : [Γ ||-S< l > arr' Γ tNat tBool]) :
    [Γ ||-EllS t ≅ t' : ℓ | RNtoB] -> [Γ ||-EllS t ≅ t' : ℓ | RNtoB'].
  Proof.
    intros Rtt'.
    destruct Rtt' eqn:eRtt'.
    constructor; tea.
    + destruct isellL; constructor; tea.
      eapply SirrLR; tea.
    + destruct isellR; constructor; tea.
      eapply SirrLR; tea.
    + eapply SirrLR; tea.
  Qed.
  Lemma irrEll {Γ l t t'} {ℓ : ell} (RNtoB RNtoB' : [Γ ||-< l > arr' Γ tNat tBool]) :
    [Γ ||-Ell t ≅ t' : ℓ | RNtoB] -> [Γ ||-Ell t ≅ t' : ℓ | RNtoB'].
  Proof.
    intros Rtt'.
    eapply (dSplit_bind_return Rtt').
    intros * oNtoB oRn oNtoB'.
    now unshelve eapply SirrEll, Rtt'.
  Qed.

  Lemma SsymmetricEll{Γ l n n' ℓ} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) :
    [Γ ||-EllS n ≅ n' : ℓ | RNtoB] -> [Γ ||-EllS n' ≅ n : ℓ | RNtoB].
  Proof.
    intros [].
    constructor; tea; symmetry; tea.
  Qed.
  Lemma symmetricEll {Γ l n n' ℓ} (RNtoB : [Γ ||-< l > arr' Γ tNat tBool]) :
    [Γ ||-Ell n ≅ n' : ℓ | RNtoB] -> [Γ ||-Ell n' ≅ n : ℓ | RNtoB].
  Proof.
    intros Rn.
    eapply (dSplit_bind_return Rn).
    intros * _ oRn oNtoB.
    unshelve eapply SirrEll, SsymmetricEll, Rn; tea.
  Qed.

  Lemma StransitiveEll {Γ l n n' n'' ℓ} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) :
    [Γ ||-EllS n ≅ n' : ℓ | RNtoB] -> [Γ ||-EllS n' ≅ n'' : ℓ | RNtoB] -> [Γ ||-EllS n ≅ n'' : ℓ | RNtoB].
  Proof.
    intros [] [].
    constructor; tea; etransitivity; tea.
  Qed.
  Lemma transitiveEll {Γ l n n' n'' ℓ} (RNtoB : [Γ ||-< l > arr' Γ tNat tBool]) :
    [Γ ||-Ell n ≅ n' : ℓ | RNtoB] -> [Γ ||-Ell n' ≅ n'' : ℓ | RNtoB] -> [Γ ||-Ell n ≅ n'' : ℓ | RNtoB].
  Proof.
    intros Rnn' Rn'n''.
    eapply (dSplit_bind Rnn').
    intros Δ wfΔ ρ _ oRnn'.
    unshelve eapply (dSplit_wk_bind_return Rn'n''); tea.
    intros * _ oRn'n'' oNtoB.
    eapply SirrEll, StransitiveEll.
    + now unshelve eapply Rnn', overtree_PSh.
    + now unshelve eapply Rn'n''.
  Qed.

  Instance SPER_Ell l Γ RNtoB ℓ : PER (EllRedTmEq (l:=l) Γ RNtoB ℓ).
  Proof.
    constructor.
    + intros n n'. eapply SsymmetricEll.
    + intros n n' n''. eapply StransitiveEll.
  Qed.
  Instance PER_Ell l Γ RNtoB ℓ : PER (WEllRedTmEq (l:=l) Γ RNtoB ℓ).
  Proof.
    constructor.
    + intros n n'. eapply symmetricEll.
    + intros n n' n''. eapply transitiveEll.
  Qed.

  Lemma wkisell {Γ Δ l t}  {ℓ : ell} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) :
    EllRedTmEq.isLREll (RNtoB:=RNtoB) (ℓ:=ℓ) t -> EllRedTmEq.isLREll (RNtoB:=wkRed (SwkLR _ _ _ RNtoB) ρ wfΔ) (ℓ:=ℓ) t⟨ρ⟩.
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros isellt.
    destruct isellt as [t' Rt Rtnb|]; rewrite <-? wk_box; constructor; tea.
    - unshelve (eapply SirrLR, SwkLR; tea); tea.
    - change [?Γ ||-Bool ?tL ≅ ?tR :Bool] with [Γ ||-S< l > tL ≅ tR :_ | SboolRed wfΔ].
      change [?Γ ||-Bool ?tL ≅ ?tR :Bool] with [Γ ||-S< l > tL ≅ tR :_ | SboolRed wfΓ] in Rtnb.
      intros n b inℓ.
      rewrite <- (wk_nat_to_term ρ), <- (wk_bool_to_term ρ), wk_app.
      now unshelve now eapply SirrLREq, SwkLR, Rtnb.
    - eapply in_ctx_wk with (d:=ℓ); tea.
  Qed.
  Lemma SwkEll {Γ Δ l t t'} {ℓ : ell} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) :
    [Γ ||-EllS t ≅ t' : ℓ | RNtoB] -> [Δ ||-EllS t⟨ρ⟩ ≅ t'⟨ρ⟩ : ℓ | wkRed (SwkLR _ _ _ RNtoB) ρ wfΔ].
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros [].
    constructor.
    1,2: refine (wkisell _ _ _ _); tea.
    1,2: eapply (ty_wk (A:=ℓ)); tea.
    1: eapply (convtm_wk (A:=ℓ)); tea.
    rewrite ! wk_eval.
    unshelve eapply SirrLR, SwkLR, eqeval; tea.
  Qed.

  Lemma WEll_return {Γ l t t'} {ℓ : ell} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool])
    (WRNtoB : [Γ ||-< l > arr' Γ tNat tBool]) :
    [Γ ||-EllS t ≅ t' : ℓ | RNtoB] -> [Γ ||-Ell t ≅ t' : ℓ | WRNtoB].
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros Rt.
    eapply Split_return; tea.
    intros ??? oRNtoB.
    unshelve eapply SirrEll, SwkEll; tea.
  Qed.


  Lemma isLREll_isWfEll {Γ l ℓ t} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]):
    EllRedTmEq.isLREll (Γ:=Γ) (RNtoB:=RNtoB) (ℓ:=ℓ) (l:=l) t -> isWfEll Γ ℓ t.
  Proof.
    intros isellt.
    assert (wfΓ :[|-Γ]) by (escape; gtyping).
    destruct isellt as [t Rt Rtnb|]; constructor; tea.
    + escape; tea.
    + intros n b inℓ.
      eapply escapeTm.
      change [?Γ ||-Bool ?tL ≅ ?tR :Bool]
        with [Γ ||-S< l > tL ≅ tR :_ | SboolRed wfΓ] in *.
      now eapply Rtnb.
  Qed.

  Lemma escapeEll {Γ l n n' ℓ} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) : [Γ ||-EllS n ≅ n' : ℓ | RNtoB] -> [Γ |- n : ℓ] × [Γ |- n' : ℓ] × [Γ |- n ≅ n' : ℓ].
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros [].
    prod_splitter; tea.
  Qed.

  Lemma SreflectEll {Γ l} {ℓ : ell} {v} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) :
    in_ctx Γ v ℓ -> [Γ ||-EllS tRel v : ℓ | RNtoB].
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros inΓ.
    constructor.
    1,2: constructor; tea.
    1,2: eapply ty_var; tea.
    1: eapply convtm_varEll; tea.
    assert [ |- Γ ,, tNat] as wfΓN by (eapply wfc_cons; gtyping).
    assert [Γ,,tNat |- tBool] as gB by
      (eapply wft_term, ty_bool; tea).
    assert [Γ |-[ ta ] arr' Γ tNat tBool ≅ arr' Γ tNat tBool] as gNtoB by
      (eapply convty_term, convtm_prod, convtm_bool; tea; gtyping).
    eapply canonPi_inv.
    unshelve eapply Build_PiRedTmEq'.
    1,2: econstructor; cbn ; [eapply redtmwf_refl, ty_eval, ty_var; tea
      | eapply EvalLRFun; cbn; tea].
    - cbn. eapply convtm_eta, convtm_convneu, (convneu_eval (k:=0)),
        convneu_var; tea.
      2,4: eapply ty_eval, ty_var; tea.
      1:gtyping.
      1,2: constructor; tea.
      1: constructor.
      1: cbn; rewrite wk_to_ren_id;
        now eapply in_there with (A:=ℓ).
      1: eapply (ty_var0 (A:=tNat)); gtyping.
    - cbn[PiRedTmEq.nf].
      intros *.
      unshelve eapply Wpack_return'.
      1: unshelve eapply SboolRed; tea.
      eapply (SevalRelRedEq (k:=0)), SirrLR, hab.
      eapply in_ctx_wk with (d:=ℓ); tea.
  Qed.
  Lemma Svar0Ell {Γ l} {ℓ : ell} (RNtoB : [Γ,,ℓ ||-S< l > arr' Γ tNat tBool]) : [Γ,,ℓ ||-EllS tRel 0 : ℓ | RNtoB].
  Proof.
    eapply SreflectEll.
    constructor.
  Qed.
  Lemma reflectEll {Γ l} {ℓ : ell} {v} (RNtoB : [Γ ||-< l > arr' Γ tNat tBool]) :
    in_ctx Γ v ℓ -> [Γ ||-Ell tRel v : ℓ | RNtoB].
  Proof.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    intros inℓ.
    unshelve now eapply WEll_return, SreflectEll.
    now eapply SNtoBRed.
  Qed.
  Lemma var0Ell {Γ l} {ℓ : ell} (RNtoB : [Γ,,ℓ ||-< l > arr' Γ tNat tBool]) : [Γ,,ℓ ||-Ell tRel 0 : ℓ | RNtoB].
  Proof.
    eapply reflectEll.
    constructor.
  Qed.

  Lemma SevalRedEq {Γ wfΓ l t t'} {ℓ : ell} :
    [ Γ ||-EllS t ≅ t' : ℓ | SNtoBRed wfΓ (l:=l)] -> [ Γ ||-S< l > tEval ℓ t ≅ tEval ℓ t' : _ | SNtoBRed wfΓ].
  Proof.
    intros Rtt'. eapply Rtt'.
  Qed.

  Lemma evalRedEq {Γ wfΓ l t t'} {ℓ : ell} :
    [ Γ ||-Ell t ≅ t' : ℓ | NtoBRed wfΓ (l:=l) ] -> [ Γ ||-< l > tEval ℓ t ≅ tEval ℓ t' : _ | NtoBRed wfΓ (l:=l)].
  Proof.
    intros Rtt'.
    eapply (dSplit_bind_return Rtt').
    intros ??? _ oRtt' oRNtoB.
    rewrite <-! wk_eval.
    unshelve eapply SirrLR, SevalRedEq, SirrEll, Rtt'; tea.
  Qed.

  Lemma SboxRed {Γ l t t'} {ℓ : ell} (wfΓ : [|-Γ]) :
    [Γ ||-S< l > t ≅ t' : _ | SNtoBRed wfΓ] ->
    (forall n b, in_ell ℓ n b ->
      [Γ ||-S< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ ]) ->
    (forall n b, in_ell ℓ n b ->
      [Γ ||-S< l > tApp t' (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]) ->
    [Γ ||-EllS tBox ℓ t ≅ tBox ℓ t' : ℓ | SNtoBRed wfΓ (l:=l)].
  Proof.
    intros Rtt' Btnb Bt'nb.
    escape. cbn in Btnb, Bt'nb.
    constructor.
    1,2: constructor.
    1: eapply lrefl; tea.
    2: eapply urefl; tea.
    3,4: eapply ty_box; tea.
    5: eapply convtm_box; tea.
    6: eapply SredSubstTmEq; tea; eapply redtm_evalBox; tea.
    1-7: intros n b inℓ.
    3-7: unshelve eapply (escapeTm (SboolRed wfΓ)); tea; cbn.
    1-7: eauto.
  Qed.

  Lemma dSplit_bind_ell {Γ} (wfΓ : [|-Γ]) {A} {ℓ : ell} {P : nat -> bool -> Monad.dPSh Γ A}
    {hA : Split A} (hP : forall n b, in_ell ℓ n b -> dSplit (P n b) hA) :
    dSplit (fun Δ wfΔ ρ hA => forall n b, in_ell ℓ n b -> P n b Δ wfΔ ρ hA) hA.
  Proof.
    induction ℓ as [| ℓ n b ihℓ] using ell_rect .
    + eapply Split_return; tea.
      intros ?????? [].
    + assert (hP' : forall n b, in_ell ℓ n b -> dSplit (P n b) hA).
      { intros n' b' inℓ'.
        eapply hP. eapply in_cons_ell. now right. }
      specialize (ihℓ hP'); clear hP'.
      specialize (hP n b ltac:(eapply in_cons_ell; left; repeat constructor)).
      eapply (dSplit_bind hP).
      intros ??? ohA ohP.
      unshelve eapply (dSplit_wk_bind_return ihℓ); tea.
      intros ??? _ oihℓ ohA' n' b' [[-> ->]| [inℓ]]%in_cons_ell_relevant.
      - now eapply hP, overtree_PSh.
      - eapply ihℓ; tea.
  Qed.

  Lemma boxRed {Γ l t t'} {ℓ : ell} (wfΓ : [|-Γ]) :
    [Γ ||-< l > t ≅ t' : _ | NtoBRed (l:=l) wfΓ] ->
    (forall n b, in_ell ℓ n b ->
      [Γ ||-< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | boolRed (l:=l) wfΓ]) ->
    [Γ ||-Ell tBox ℓ t ≅ tBox ℓ t' : ℓ | NtoBRed (l:=l) wfΓ].
  Proof.
    intros Rtt' Rtnb.
    assert (Rt'nb : forall n b, in_ell ℓ n b ->
      [Γ ||-< l > tApp t' (nat_to_term n) ≅ bool_to_term b : _ | boolRed (l:=l) wfΓ]).
    { intros ?? inℓ.
      specialize (Rtnb _ _ inℓ).
      etransitivity; tea.
      symmetry.
      eapply simple_appcongTerm; tea.
      now unshelve eapply nat_to_termReq. }
    eapply dSplit_bind_ell in Rtnb; tea.
    eapply dSplit_bind_ell in Rt'nb; tea.
    eapply (dSplit_bind Rtt'). Unshelve.
    intros Δ wfΔ ρ _ oRtt'.
    unshelve eapply (dSplit_wk_bind Rtnb); tea.
    intros Ξ wfΞ ρΞ _ oRtnb.
    unshelve eapply (dSplit_wk_bind_return Rt'nb); tea.
    { eapply wk_well_wk_compose; tea. }
    intros Ω wfΩ ρΩ obool oRt'nb oNtoR.
    rewrite <-! wk_box.
    unshelve eapply SirrEll, SboxRed; tea.
    - now unshelve eapply SirrLR, Rtt', overtree_PSh.
    - intros n b inℓ.
      rewrite <- (wk_nat_to_term ((ρΩ ∘w ρΞ) ∘w ρ)),
        <- (wk_bool_to_term ((ρΩ ∘w ρΞ) ∘w ρ)).
      unshelve eapply SirrLR, Rtnb; tea.
      all: rewrite wk_comp_assoc; tea.
      now eapply overtree_PSh.
    - intros n b inℓ.
      rewrite <- (wk_nat_to_term ((ρΩ ∘w ρΞ) ∘w ρ)),
        <- (wk_bool_to_term ((ρΩ ∘w ρΞ) ∘w ρ)).
      unshelve eapply SirrLR, Rt'nb; tea.
      all: now rewrite wk_comp_assoc.
  Qed.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-S< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-S<_> _ ≅ _  : _ | ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTm RA H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-<_> _ ≅ _  : _ | ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTm _ H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-EllS _ ≅ _ : _ | _] |- _] =>
    try
      (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeEll _ H) as (Xl & Xr & X) );
      block H
  end; unblock.


  Lemma Sevalnat_to_termRed {Γ l n k b} {ℓ : ell} (wfΓ : [|-Γ]) : in_ell ℓ k b -> [Γ ||-EllS n : ℓ | SNtoBRed (l:=l) wfΓ] ->
    [Γ ||-S< l > tApp (tEval ℓ n) (nat_to_term k) ≅ bool_to_term b : _ | SboolRed wfΓ].
  Proof.
    intros inℓ Rnn'.
    destruct Rnn' as [[t Rt Rtb|] elln' gn gn' geqnn' Reval].
    - eapply SredSubstLeftTmEq.
      2: eapply (redtm_app (B:=tBool)), ty_nSucc, ty_zero; tea.
      2: eapply redtm_evalBox; tea.
      2: escape; tea.
      2: clear n b inℓ; intros n b inℓ;
        unshelve eapply (escapeTm (SboolRed wfΓ)), Rtb; tea.
      eapply Rtb; tea.
    - eapply SredSubstLeftTmEq, redtm_evalRel; tea.
      eapply Sbool_to_termRed.
  Qed.
  Lemma evalnat_to_termRed {Γ l n k b} {ℓ : ell} (wfΓ : [|-Γ]) : in_ell ℓ k b -> [Γ ||-Ell n : ℓ | NtoBRed (l:=l) wfΓ] ->
    [Γ ||-< l > tApp (tEval ℓ n) (nat_to_term k) ≅ bool_to_term b : _ | boolRed (l:=l) wfΓ].
  Proof.
    intros inℓ Rnn'.
    eapply (dSplit_bind_return Rnn').
    intros * oNtoR oRnn' oB.
    rewrite <- wk_app, <- wk_eval, wk_nat_to_term, wk_bool_to_term.
    now unshelve eapply SirrLR, Sevalnat_to_termRed, SirrEll, Rnn'.
  Qed.

(*   Lemma evalnat_to_term {ℓ : ell} {Γ l t n b} (RNtoB : [Γ ||-S< l > arr' Γ tNat tBool]) : in_ell ℓ n b ->
    [Γ ||-EllS t : ℓ |RNtoB] -> [Γ ||-Bool tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b :Bool].
  Proof.
    intros inℓ Rt.
    assert (wfΓ : [|-Γ]) by (escape; gtyping).
    eapply evalnat_to_termRed with (wfΓ:=wfΓ); tea.
    now eapply SirrEll.
  Qed.
 *)
  Lemma SevalBoxRed {Γ l t} (wfΓ : [|-Γ]) {ℓ : ell} :
    (forall n b, in_ell ℓ n b -> [Γ ||-S< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]) ->
    [Γ ||-S< l > t :_ | SNtoBRed wfΓ] -> [Γ ||-S< l > tEval ℓ (tBox ℓ t) ≅ t : _ | SNtoBRed wfΓ].
  Proof.
    intros Rtnb Rt.
    eapply SredSubstLeftTmEq, redtm_evalBox; tea.
    2: intros n b inℓ; specialize (Rtnb _ _ inℓ).
    all: escape; tea.
  Qed.

  Lemma SboxEvalRedEq {Γ l ℓ t t'} (wfΓ : [|-Γ]) :
    [Γ ||-EllS t ≅ t' : ℓ | SNtoBRed wfΓ (l:=l)] ->
    [Γ ||-EllS tBox ℓ (tEval ℓ t) ≅ tBox ℓ (tEval ℓ t') : ℓ | SNtoBRed wfΓ (l:=l)].
  Proof.
    intros Rt.
    unshelve eapply SboxRed; tea.
    { eapply Rt. }
    1,2: intros; eapply Sevalnat_to_termRed; tea.
    + eapply lrefl; tea.
    + eapply urefl; tea.
  Qed.

  Lemma SetaEllRed {Γ l ℓ t} (wfΓ : [|-Γ]) :
    [Γ ||-EllS t : ℓ | SNtoBRed wfΓ (l:=l)] ->
    [Γ ||-EllS tBox ℓ (tEval ℓ t) ≅ t : ℓ | SNtoBRed wfΓ (l:=l)].
  Proof.
    intros Rt.
    destruct Rt eqn:eRt.
    constructor; tea.
    + constructor; tea.
      intros n b inℓ; unshelve eapply Sevalnat_to_termRed, lrefl, SirrEll; tea.
    + eapply escapeEll.
      eapply SboxEvalRedEq; tea.
    + escape.
      eapply convtm_eta_ell; tea.
      - eapply escapeEll.
        eapply SboxEvalRedEq; tea.
      - constructor; tea.
        intros n b inℓ.
        eapply escapeTm, Sevalnat_to_termRed; tea.
      - now eapply isLREll_isWfEll.
      - eapply escapeTm, SevalBoxRed, Rt.
        intros n b inℓ.
        eapply Sevalnat_to_termRed; tea.
    + eapply SevalBoxRed, Rt.
      intros n b inℓ.
      eapply Sevalnat_to_termRed; tea.
  Qed.


  Section SEllElimRedEq.
  Context {Γ l ℓ k P P' t t' b b'} (wfΓ : [|-Γ]) (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false)
    (RB := SboolRed (l:=l) wfΓ) (RN := SnatRed (l:=l) wfΓ)
    (RNtoB := SNtoBRed (l:=l) wfΓ)
    (gP : [Γ,,ℓ |- P]) (gP' : [Γ,,ℓ |- P']) (gPP' : [Γ,,ℓ |- P ≅ P'])
    (RPP'ext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall t t', [Δ ||-EllS t ≅ t' : ℓ | SNtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[t..] ≅ P'⟨wk_up ℓ ρ⟩[t'..]])
    (Rt  : [Γ ||-EllS t ≅ t' : ℓ | RNtoB]) (Rb : [Γ ||-S< l > b ≅ b' : tBool | RB])
    (Rtkb : [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term k) ≅ b : tBool | RB])
    (Rt'kb : [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term k) ≅ b : tBool | RB])
    (Pt := P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
    (Pf := P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..])
    (P't := P'⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
    (P'f := P'⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..])
    (wfΓℓ := wfc_consell (ℓ:=ℓ) wfΓ)
    (wfΓℓt := wfc_consell (ℓ:=ℓt) wfΓ)
    (wfΓℓf := wfc_consell (ℓ:=ℓf) wfΓ).
  Let RPP' : [Γ,,ℓ ||-< l > P ≅ P'].
  Proof.
    rewrite <- (wk1_eta (Γ:=Γ) (A:=ℓ) (t:=P)), <- (wk1_eta (Γ:=Γ) (A:=ℓ) (t:=P')).
    unshelve eapply RPP'ext; tea.
    eapply SreflectEll.
    repeat constructor.
  Qed.
  Let RPP'extt : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-EllS n ≅ n' : ℓt | SNtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n))..] ≅ P'⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n'))..]].
  Proof.
    intros * Rn0.
    unshelve eapply RPP'ext; tea.
    eapply SboxRed.
    + eapply SevalRedEq; tea.
    + intros ?? inℓ.
      eapply Sevalnat_to_termRed, lrefl; tea.
      eapply in_cons_ell; right; tea.
    + intros ?? inℓ.
      eapply Sevalnat_to_termRed, urefl; tea.
      eapply in_cons_ell; right; tea.
  Qed.
  Let RPP'extf : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-EllS n ≅ n' : ℓf | SNtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n))..] ≅ P'⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n'))..]].
  Proof.
    intros * Rn0.
    unshelve eapply RPP'ext; tea.
    eapply SboxRed.
    + eapply SevalRedEq; tea.
    + intros ?? inℓ.
      eapply Sevalnat_to_termRed, lrefl; tea.
      eapply in_cons_ell; right; tea.
    + intros ?? inℓ.
      eapply Sevalnat_to_termRed, urefl; tea.
      eapply in_cons_ell; right; tea.
  Qed.

  Let RPP't : [Γ ||-< l > P[t..] ≅ P'[t'..]].
  Proof.
    rewrite <- (wk_id_ren_on (Γ,,ℓ) P), <- (wk_id_ren_on (Γ,,ℓ) P'),
      <- 2 wk_up_wk_id.
    unshelve eapply RPP'ext; tea.
  Qed.
  Context {ht ht' hf hf'}
    (Rhtext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n' (Rn : [Δ ||-EllS n ≅ n' : ℓt | SNtoBRed (l:=l) wfΔ]),
      [Δ ||-< l > ht⟨wk_up ℓt ρ⟩[n..] ≅ ht'⟨wk_up ℓt ρ⟩[n'..] :
        P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n))..] | RPP'extt Δ ρ wfΔ _ _ Rn])
    (Rhfext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n' (Rn : [Δ ||-EllS n ≅ n' : ℓf | SNtoBRed (l:=l) wfΔ]),
      [Δ ||-< l > hf⟨wk_up ℓf ρ⟩[n..] ≅ hf'⟨wk_up ℓf ρ⟩[n'..] :
        P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n))..] | RPP'extf Δ ρ wfΔ _ _ Rn]).
(*     (Rht : [Γ,,ℓt ||-< l > ht ≅ ht' : _ |RPP't])
    (Rhf : [Γ,,ℓf ||-< l > hf ≅ hf' : _ |RPP'f]). *)

  Let RPext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-EllS n ≅ n' : ℓ | SNtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[n..] ≅ P⟨wk_up ℓ ρ⟩[n'..]].
  Proof.
    intros * Rn0.
    etransitivity; [|symmetry]; eapply RPP'ext.
    1: eapply Rn0.
    eapply urefl; tea.
  Qed.

  Let RPP'tt := RPP'extt _ (wk1 ℓt) wfΓℓt _ _ (Svar0Ell _).
  Let Rht : [Γ,,ℓt ||-< l > ht ≅ ht' : _|RPP'tt].
  Proof.
    specialize (Rhtext _ (wk1 ℓt) wfΓℓt _ _ (Svar0Ell _)) as Rht.
    now rewrite ! wk1_eta in Rht.
  Qed.
  Let RPP'ff := RPP'extf _ (wk1 ℓf) wfΓℓf _ _ (Svar0Ell _).
  Let Rhf : [Γ,,ℓf ||-< l > hf ≅ hf' : _|RPP'ff].
  Proof.
    specialize (Rhfext _ (wk1 ℓf) wfΓℓf _ _ (Svar0Ell _)) as Rhf.
    now rewrite ! wk1_eta in Rhf.
  Qed.

  Lemma SEllElimRedEqAux : forall b b' (Rbb' : BoolPropEq Γ b b')
    (Rnb : [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term k) ≅ b : tBool | RB])
    (Rn'b : [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term k) ≅ b : tBool | RB]),
    [Γ ||-< l > tEllElim k ℓ P ht hf t b ≅ tEllElim k ℓ P' ht' hf' t' b' : P[t..] | RPP't].
  Proof.
    clear dependent b. clear b'.
    intros ?? propbb' Rnb Rn'b.
    destruct propbb'.
    - escape.
      eapply redSubstTmEq.
      2: eapply redtm_ellElimTrue; tea.
      2:{ eapply redtm_ellElimTrue; tea.
        1,2 : eapply ty_conv; tea. }
      rewrite <- (wk_id_ren_on (Γ,,ℓt) ht), <- (wk_id_ren_on (Γ,,ℓt) ht'),
        <-2 wk_up_wk_id.
      assert (Rtnbt : forall n b, in_ell ℓt n b ->
        [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply Sevalnat_to_termRed, lrefl; tea. }
      assert (Rt'nbt : forall n b, in_ell ℓt n b ->
        [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply Sevalnat_to_termRed, urefl; tea. }
      assert (Rboxeval : [Γ ||-EllS tBox ℓt (tEval ℓ t) ≅ tBox ℓt (tEval ℓ t'): ℓt | SNtoBRed (l:=l) wfΓ]).
      { eapply SboxRed; tea.
        eapply Rt. }
      unshelve eapply irrLRConv, Rhtext; tea.
      replace P[t..] with P⟨wk_up ℓ (@wk_id Γ)⟩[t..] by
        now rewrite wk_up_wk_id, wk_id_ren_on.
      unshelve eapply RPext; tea.
      etransitivity.
      + eapply SboxRed; tea.
        { eapply SevalBoxRed, lrefl, Rt; tea. }
        * intros n b inℓ.
          eapply Sevalnat_to_termRed, lrefl; tea.
          eapply in_cons_ell; right; tea.
        * intros n b inℓ.
          eapply Sevalnat_to_termRed, lrefl; tea.
      + now eapply SetaEllRed, lrefl.
    - escape.
      eapply redSubstTmEq.
      2: eapply redtm_ellElimFalse; tea.
      2:{ eapply redtm_ellElimFalse; tea.
        1,2 : eapply ty_conv; tea. }
      rewrite <- (wk_id_ren_on (Γ,,ℓf) hf), <- (wk_id_ren_on (Γ,,ℓf) hf'),
        <-2 wk_up_wk_id.
      assert (Rtnbf : forall n b, in_ell ℓf n b ->
        [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply Sevalnat_to_termRed, lrefl; tea. }
      assert (Rt'nbf : forall n b, in_ell ℓf n b ->
        [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply Sevalnat_to_termRed, urefl; tea. }
      assert (Rboxeval : [Γ ||-EllS tBox ℓf (tEval ℓ t) ≅ tBox ℓf (tEval ℓ t'): ℓf | SNtoBRed (l:=l) wfΓ]).
      { eapply SboxRed; tea.
        eapply Rt. }
      unshelve eapply irrLRConv, Rhfext; tea.
      replace P[t..] with P⟨wk_up ℓ (@wk_id Γ)⟩[t..] by
        now rewrite wk_up_wk_id, wk_id_ren_on.
      unshelve eapply RPext; tea.
      etransitivity.
      + eapply SboxRed; tea.
        { eapply SevalBoxRed, lrefl, Rt; tea. }
        * intros n b inℓ.
          eapply Sevalnat_to_termRed, lrefl; tea.
          eapply in_cons_ell; right; tea.
        * intros n b inℓ.
          eapply Sevalnat_to_termRed, lrefl; tea.
      + now eapply SetaEllRed, lrefl.
  - epose proof (SneNfTermEq RB r).
    escape.
    unshelve eapply irrLR, neNfTermEq; tea.
    { now eapply lrefl. }
    constructor.
    + eapply ty_ellElim; tea.
    + eapply ty_conv.
      { eapply ty_ellElim; tea.
        - eapply ty_conv; tea.
        - eapply ty_conv; tea.
        - etransitivity; tea. }
      now symmetry.
    + destruct r; eapply convneu_ellElim; tea.
  Qed.

  Lemma SEllElimRedEq :
    [Γ ||-< l > tEllElim k ℓ P ht hf t b ≅ tEllElim k ℓ P' ht' hf' t' b' : P[t..] | RPP't].
  Proof.
    destruct Rb as [?? [] []].
    escape.
    eapply redSubstTmEq.
    2,3: eapply redtm_ellElim; tea.
    2,3: eapply ty_conv; tea.
    2: etransitivity; tea.
    eapply SEllElimRedEqAux; tea.
    1,2: etransitivity; tea.
    1,2: eapply SredSubstLeftTmEq; tea; eapply lrefl; tea;
      eexists nfL nfR; tea; eapply redtmwf_refl; tea.
  Qed.
End SEllElimRedEq.

  Section EllElimRedEq.
  Context {Γ l ℓ k P P' t t' b b'} (wfΓ : [|-Γ]) (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false)
    (RB := boolRed (l:=l) wfΓ) (RN := natRed (l:=l) wfΓ)
    (RNtoB := NtoBRed (l:=l) wfΓ)
    (gP : [Γ,,ℓ |- P]) (gP' : [Γ,,ℓ |- P']) (gPP' : [Γ,,ℓ |- P ≅ P'])
    (RPP'ext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]),
      forall t t', [Δ ||-Ell t ≅ t' : ℓ | NtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[t..] ≅ P'⟨wk_up ℓ ρ⟩[t'..]])
    (Rt  : [Γ ||-Ell t ≅ t' : ℓ | RNtoB]) (Rb : [Γ ||-< l > b ≅ b' : tBool | RB])
    (Rtkb : [Γ ||-< l > tApp (tEval ℓ t) (nat_to_term k) ≅ b : tBool | RB])
    (Rt'kb : [Γ ||-< l > tApp (tEval ℓ t') (nat_to_term k) ≅ b : tBool | RB])
    (Pt := P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
    (Pf := P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..])
    (P't := P'⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
    (P'f := P'⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..])
    (wfΓℓ := wfc_consell (ℓ:=ℓ) wfΓ)
    (wfΓℓt := wfc_consell (ℓ:=ℓt) wfΓ)
    (wfΓℓf := wfc_consell (ℓ:=ℓf) wfΓ).
  Let RPP' : [Γ,,ℓ ||-< l > P ≅ P'].
  Proof.
    rewrite <- (wk1_eta (Γ:=Γ) (A:=ℓ) (t:=P)), <- (wk1_eta (Γ:=Γ) (A:=ℓ) (t:=P')).
    unshelve eapply RPP'ext; tea.
    eapply reflectEll.
    repeat constructor.
  Qed.
  Let RPP'extt : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-Ell n ≅ n' : ℓt | NtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n))..] ≅ P'⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n'))..]].
  Proof.
    intros * Rn0.
    unshelve eapply RPP'ext; tea.
    eapply boxRed.
    + eapply evalRedEq; tea.
    + intros ?? inℓ.
      eapply evalnat_to_termRed, lrefl; tea.
      eapply in_cons_ell; right; tea.
  Qed.
  Let RPP'extf : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-Ell n ≅ n' : ℓf | NtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n))..] ≅ P'⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n'))..]].
  Proof.
    intros * Rn0.
    unshelve eapply RPP'ext; tea.
    eapply boxRed.
    + eapply evalRedEq; tea.
    + intros ?? inℓ.
      eapply evalnat_to_termRed, lrefl; tea.
      eapply in_cons_ell; right; tea.
  Qed.

  Let RPP't : [Γ ||-< l > P[t..] ≅ P'[t'..]].
  Proof.
    rewrite <- (wk_id_ren_on (Γ,,ℓ) P), <- (wk_id_ren_on (Γ,,ℓ) P'),
      <- 2 wk_up_wk_id.
    unshelve eapply RPP'ext; tea.
  Qed.
  Context {ht ht' hf hf'}
    (Rhtext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n' (Rn : [Δ ||-Ell n ≅ n' : ℓt | NtoBRed (l:=l) wfΔ]),
      [Δ ||-< l > ht⟨wk_up ℓt ρ⟩[n..] ≅ ht'⟨wk_up ℓt ρ⟩[n'..] : P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓt n))..] | RPP'extt Δ ρ wfΔ _ _ Rn])
    (Rhfext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n' (Rn : [Δ ||-Ell n ≅ n' : ℓf | NtoBRed (l:=l) wfΔ]),
      [Δ ||-< l > hf⟨wk_up ℓf ρ⟩[n..] ≅ hf'⟨wk_up ℓf ρ⟩[n'..] : P⟨wk_up ℓ ρ⟩[(tBox ℓ (tEval ℓf n))..] | RPP'extf Δ ρ wfΔ _ _ Rn]).
(*     (Rht : [Γ,,ℓt ||-< l > ht ≅ ht' : _ |RPP't])
    (Rhf : [Γ,,ℓf ||-< l > hf ≅ hf' : _ |RPP'f]). *)

  Let RPext : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), forall n n', [Δ ||-Ell n ≅ n' : ℓ | NtoBRed (l:=l) wfΔ] ->
      [Δ ||-< l > P⟨wk_up ℓ ρ⟩[n..] ≅ P⟨wk_up ℓ ρ⟩[n'..]].
  Proof.
    intros * Rn0.
    etransitivity; [|symmetry]; eapply RPP'ext.
    1: eapply Rn0.
    eapply urefl; tea.
  Qed.

  Let RPP'tt := RPP'extt _ (wk1 ℓt) wfΓℓt _ _ (var0Ell _).
  Let Rht : [Γ,,ℓt ||-< l > ht ≅ ht' : _|RPP'tt].
  Proof.
    specialize (Rhtext _ (wk1 ℓt) wfΓℓt _ _ (var0Ell _)) as Rht.
    now rewrite ! wk1_eta in Rht.
  Qed.
  Let RPP'ff := RPP'extf _ (wk1 ℓf) wfΓℓf _ _ (var0Ell _).
  Let Rhf : [Γ,,ℓf ||-< l > hf ≅ hf' : _|RPP'ff].
  Proof.
    specialize (Rhfext _ (wk1 ℓf) wfΓℓf _ _ (var0Ell _)) as Rhf.
    now rewrite ! wk1_eta in Rhf.
  Qed.

(*   Lemma SEllElimRedEqAux : forall b b' (Rbb' : BoolPropEq Γ b b')
    (Rnb : [Γ ||-< l > tApp (tEval ℓ t) (nat_to_term k) ≅ b : tBool | RB])
    (Rn'b : [Γ ||-< l > tApp (tEval ℓ t') (nat_to_term k) ≅ b : tBool | RB]),
    [Γ ||-< l > tEllElim k ℓ P ht hf t b ≅ tEllElim k ℓ P' ht' hf' t' b' : P[t..] | RPP't].
  Proof.
    clear dependent b. clear b'.
    intros ?? propbb' Rnb Rn'b.
    destruct propbb'.
    - escape.
      eapply redSubstTmEq.
      2: eapply redtm_ellElimTrue; tea.
      2:{ eapply redtm_ellElimTrue; tea.
        1,2 : eapply ty_conv; tea. }
      rewrite <- (wk_id_ren_on (Γ,,ℓt) ht), <- (wk_id_ren_on (Γ,,ℓt) ht'),
        <-2 wk_up_wk_id.
      assert (Rtnbt : forall n b, in_ell ℓt n b ->
        [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply evalnat_to_termRed; tea. }
      assert (Rt'nbt : forall n b, in_ell ℓt n b ->
        [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply evalnat_to_termRed; tea; symmetry; tea. }
      assert (Rboxeval : [Γ ||-EllS tBox ℓt (tEval ℓ t) ≅ tBox ℓt (tEval ℓ t'): ℓt | SNtoBRedEqTy (l:=l) wfΓ]).
      { eapply SboxRed; tea.
        eapply Rt. }
      unshelve eapply irrLRConv, Rhtext; tea.
      replace P[t..] with P⟨wk_up ℓ (@wk_id Γ)⟩[t..] by
        now rewrite wk_up_wk_id, wk_id_ren_on.
      unshelve eapply RPext; tea.
      etransitivity.
      + eapply SboxRed; tea.
        { eapply evalBoxRed, lrefl, Rt; tea. }
        * intros n b inℓ.
          eapply evalnat_to_termRed; tea.
          eapply in_cons_ell; right; tea.
        * intros n b inℓ.
          eapply evalnat_to_termRed; tea.
      + now eapply etaEllRed, lrefl.
    - escape.
      eapply redSubstTmEq.
      2: eapply redtm_ellElimFalse; tea.
      2:{ eapply redtm_ellElimFalse; tea.
        1,2 : eapply ty_conv; tea. }
      rewrite <- (wk_id_ren_on (Γ,,ℓf) hf), <- (wk_id_ren_on (Γ,,ℓf) hf'),
        <-2 wk_up_wk_id.
      assert (Rtnbf : forall n b, in_ell ℓf n b ->
        [Γ ||-S< l > tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply evalnat_to_termRed; tea. }
      assert (Rt'nbf : forall n b, in_ell ℓf n b ->
        [Γ ||-S< l > tApp (tEval ℓ t') (nat_to_term n) ≅ bool_to_term b : _ | SboolRed wfΓ]).
      { intros n b [[-> ->]| [inℓ]]%in_cons_ell_relevant; tea.
        eapply evalnat_to_termRed; tea; symmetry; tea. }
      assert (Rboxeval : [Γ ||-EllS tBox ℓf (tEval ℓ t) ≅ tBox ℓf (tEval ℓ t'): ℓf | SNtoBRedEqTy (l:=l) wfΓ]).
      { eapply SboxRed; tea.
        eapply Rt. }
      unshelve eapply irrLRConv, Rhfext; tea.
      replace P[t..] with P⟨wk_up ℓ (@wk_id Γ)⟩[t..] by
        now rewrite wk_up_wk_id, wk_id_ren_on.
      unshelve eapply RPext; tea.
      etransitivity.
      + eapply SboxRed; tea.
        { eapply evalBoxRed, lrefl, Rt; tea. }
        * intros n b inℓ.
          eapply evalnat_to_termRed; tea.
          eapply in_cons_ell; right; tea.
        * intros n b inℓ.
          eapply evalnat_to_termRed; tea.
      + now eapply etaEllRed, lrefl.
  - epose proof (SneNfTermEq RB r).
    escape.
    eapply irrLR, neNfTermEq; constructor.
    + eapply ty_ellElim; tea.
    + eapply ty_conv.
      { eapply ty_ellElim; tea.
        - eapply ty_conv; tea.
        - eapply ty_conv; tea.
        - etransitivity; tea. }
      now symmetry.
    + destruct r; eapply convneu_ellElim; tea.
  Unshelve.
  tea.
  eapply lrefl; tea.
  Qed. *)

  Lemma SEllElimRedEq :
    [Γ ||-< l > tEllElim k ℓ P ht hf t b ≅ tEllElim k ℓ P' ht' hf' t' b' : P[t..] | RPP't].
  Proof.
    destruct Rb as [?? [] []].
    escape.
    eapply redSubstTmEq.
    2,3: eapply redtm_ellElim; tea.
    2,3: eapply ty_conv; tea.
    2: etransitivity; tea.
    eapply SEllElimRedEqAux; tea.
    1,2: etransitivity; tea.
    1,2: eapply SredSubstLeftTmEq; tea; eapply lrefl; tea;
      eexists nfL nfR; tea; eapply redtmwf_refl; tea.
  Qed.
End SEllElimRedEq.
End Ell.
End Ell.

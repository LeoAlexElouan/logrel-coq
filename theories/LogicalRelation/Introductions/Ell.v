From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application Nat Bool SimpleArr.

Section Ell.
  Context `{GenericTypingProperties}.

  Lemma SNtoBRedEqTy {Γ : context} (wfΓ : [|-Γ]) {l} : [Γ ||-S< l > arr' Γ tNat tBool ].
  Proof.
    eapply SArrRedTy.
    + intros. eapply SnatRed; tea.
    + intros. eapply SboolRed; tea.
  Qed.


  Lemma EvalRelRedEqAux {ℓ : ell} {Γ l v} (wfΓ : [|-Γ]) : in_ctx Γ v ℓ -> (forall tL tR (Rt : [Γ ||-Nat tL ≅ tR :Nat]), forall k,
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


  Lemma EvalRelRedEq {ℓ : ell} {Γ l v t t' k} (wfΓ :[|-Γ]):  in_ctx Γ v ℓ -> [Γ ||-S< l > t ≅ t' : tNat | SnatRed (l:=l) wfΓ ] ->
    [ Γ ||-S< l > tApp (tEval ℓ (tRel v)) (nSucc k t) ≅ tApp (tEval ℓ (tRel v)) (nSucc k t') : tBool |SboolRed wfΓ].
  Proof.
    cbn.
    intros inv Rtt'.
    eapply (fst (EvalRelRedEqAux wfΓ inv)); tea.
    Unshelve. tea.
  Qed.

  Lemma EvalRedEq {Γ l t t'} {ℓ : ell} (wfΓ : [|-Γ]) (RNtoB : [Γ ||-S<l> arr' Γ tNat tBool])
     : [ Γ ||-EllS t ≅ t' : ℓ | RNtoB ] -> [ Γ ||-S< l > tEval ℓ t ≅ tEval ℓ t' : _ | RNtoB].
  Proof.
    intros Rtt'.
    destruct Rtt' as [?? Rtt' Rconv|].
    + escape.
      eapply SredSubstTmEq; tea.
      all: eapply redtm_evalBox; tea.
      all: intros n b inℓ; specialize (Rconv n b inℓ).
      2: etransitivity.
      1,3 : eapply (escapeTm (SboolRed _)); tea.
      symmetry.
      eapply (escapeSplitTm (boolRed ltac:(tea))).
      eapply (appcongTerm _ (Wpack_return Rtt')).
      unshelve eapply Wpack_return, nat_to_termReq; tea.
      eapply natRedTy; tea.
    + eapply canonPi_inv. cbn.
      assert [ |- Γ ,, tNat] by (eapply wfc_cons; gtyping).
      assert [Γ,,tNat |- tBool] as HB by
        (eapply wft_term, ty_bool; tea).
      assert [Γ |-[ ta ] tProd tNat tBool ≅ arr' Γ tNat tBool] as Harr by
        (eapply convty_term, convtm_prod, convtm_bool; tea; gtyping).
      unshelve econstructor.
      1,2 :  econstructor; cbn; [ eapply redtmwf_refl, ty_eval, ty_var; tea
        |eapply EvalLRFun; cbn; tea].
      - cbn. eapply convtm_eta, convtm_convneu, (convneu_eval (k:=0)),
          convneu_var; tea.
        2,4: eapply ty_eval, ty_var; tea.
        1:gtyping.
        1,2: constructor; tea.
        1: constructor. Search _wk_id.
        1: cbn; rewrite wk_to_ren_id;
          now eapply in_there with (A:=ℓ).
        1: eapply (ty_var0 (A:=tNat)); gtyping.
      - cbn[PiRedTmEq.nf]. unfold PiRedTmEq.appRed.
        intros ???? wfΔ ?.
        eapply Split_return; tea.
        intros Ξ wfΞ ρΞ oRΠ.
        unshelve eapply SirrLR, SwkLR.
        3: eapply SboolRed; tea.
        all:tea. cbn.
        unshelve eapply (EvalRelRedEq (k:=0)), SirrLR, hab; tea.
        eapply in_ctx_wk with (d:=ℓ); tea.
        Unshelve. all: tea.
  Qed.

End Ell.

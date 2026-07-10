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

  Lemma EvalRedEq {l Γ t t'} {ℓ : ell} (wfΓ : [|-Γ]) (RNtoB : [Γ ||-S<l> arr' Γ tNat tBool])
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
          now eapply in_there with (A:=ℓ). Search tRel typing.
        1: eapply (ty_var0 (A:=tNat)); gtyping.
      - cbn[PiRedTmEq.nf]. unfold PiRedTmEq.appRed.
        intros ???? wfΔ ?.
        enough [ _ ||-<l>
          tApp (tEval ℓ (tRel v))⟨ρ⟩ a ≅ tApp (tEval ℓ (tRel v))⟨ρ⟩ b : _ |boolRed (l:=l) wfΔ].
        eapply Split_hom_PSh, X.
        intros Ξ wfΞ ρΞ oRΠ ?.
        unshelve eapply SirrLR, oRΠ.
        cbn.
        intros
        eapply Split_return; tea.
        intros Ξ wfΞ ρΞ oRΠ.
        eapply wkLRTm.



Definition toto (x y : nat) := y.
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

Section NatRedUndernSucc.
  Context {Γ} {wfΓ : [|-Γ]} {f : term -> term} {A}
    (hf : forall t u, [Γ |- t :⤳*: u : tNat] -> forall n, [Γ |- f (nSucc n t) :⤳*: f (nSucc n u) : A]).

  Inductive NatPropEqInst : term -> term -> Set :=
    | natReqInst n : NatPropEqInst (nat_to_term n) (nat_to_term n)
    | neReqInst n neL neR : [Γ ||-NeNf neL ≅ neR : tNat] ->
        NatPropEqInst (nSucc n neL) (nSucc n neR).

  Record NatRedTmEqInst tL tR : Set :=
    {
      nfLInst : term ;
      nfRInst : term ;
      redLInst : forall n, [Γ |- f (nSucc n tL) :⤳*: f (nSucc n nfLInst) : A] ;
      redRInst : forall n, [Γ |- f (nSucc n tR) :⤳*: f (nSucc n nfRInst) : A ] ;
  (*     eqInst : [Γ |- nfL ≅ nfR : tBool] ; *)
      propInst : NatPropEqInst nfLInst nfRInst
    }.

  Definition natRed_toInst :
    (forall tL tR (Rt : [Γ ||-Nat tL ≅ tR :Nat]), NatRedTmEqInst tL tR) ×
    (forall tL tR (propt : NatPropEq Γ tL tR), NatRedTmEqInst tL tR).
  Proof.
    apply NatRedEqInduction.
    + intros tL tR ???? _ _ [dnfL dnfR redL' redR' prop].
      econstructor; tea.
      1,2: now etransitivity; [eapply hf |].
    + econstructor.
      3: eapply (natReqInst 0).
      all: intros n; eapply redtmwf_refl. ty_simple_app, ty_nSucc; gtyping.
    + intros tL tR Rt [dnfL dnfR redL redR prop].
      eexists (tSucc dnfL) (tSucc dnfR).
      - intros n. rewrite 2nSuccswap.
        refine (redL (S n)).
      - intros n. rewrite 2nSuccswap.
        refine (redR (S n)).
      - destruct prop.
        * eapply (natReqInst (S n)).
        * now eapply (neReqInst (S n)).
    + intros neL neR Rne.
      exists neL neR.
      1,2: intros n; eapply redtmwf_refl, ty_simple_app, ty_nSucc, Rne ; gtyping.
      now eapply (neReqInst 0).
  Defined.
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
          now eapply in_there with (A:=ℓ).
        1: eapply (ty_var0 (A:=tNat)); gtyping.
      - cbn[PiRedTmEq.nf]. unfold PiRedTmEq.appRed.
        intros ???? wfΔ ?.
        eapply Split_return; tea.
        intros Ξ wfΞ ρΞ oRΠ.
        unshelve eapply SirrLR, SwkLR.
        3: eapply SboolRed; tea.
        all:tea.
        constructor.
        1:{ reflexivity. f_equal.
        unshelve eapply SirrLR, oRΠ.
        cbn.
        intros
        eapply Split_return; tea.
        intros Ξ wfΞ ρΞ oRΠ.
        eapply wkLRTm.



Definition toto (x y : nat) := y.
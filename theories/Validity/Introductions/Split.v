From Stdlib Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Nat Bool.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics Nat Bool.

Section FSnoc.
  Context `{GenericTypingProperties}.

  Lemma FequivValid {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) : Γ =ε Γ'.
  Proof.
    induction Γ, Γ', VΓ using validity_rect; tea.
  Qed.

(*   Lemma FSnocValidTy {Γ} {new} A . *)

  Lemma validFSnoc {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b}:
    new = new' :> nat -> [||-v Γ,, new ↦ b ≅ Γ',, new' ↦ b].
  Proof.
    intros.
    induction Γ, Γ', VΓ using validity_rect.
    + eapply validEmpty, Fequiv_Fup; now symmetry.
    + change [||-v Γ,, new ↦ b,,A ≅ Γ',, new' ↦ b,,A'].
      eapply validSnoc.
      constructor.
      intros * h.
      eapply (wkValidTy (wk_Fstep (new : newnat Γ) b wk_id)) in VA.
      rewrite 2!wk_Fstep_ren_on,  2!wk_id_ren_on in VA.
      eapply VA, h.
      Unshelve.
      easy.
  Defined.

  Lemma irrSubstEq {Γ0 Γ0' Γ1 Γ1'} {VΓ0 : [||-v Γ0 ≅ Γ0']} {VΓ1 : [||-v Γ1 ≅ Γ1']} :
    Γ0 = Γ1 ->
    forall {Δ} (wfΔ : [|- Δ]) {σ σ'},
    [Δ ||-v σ ≅ σ' : _ | VΓ0 | wfΔ ] ->
    [Δ ||-v σ ≅ σ' : _ | VΓ1 | wfΔ ].
  Proof.
    intros <- *.
    eapply convSubst.
  Qed.

  Lemma validFSnocSubst_in {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b σ σ'} {Δ wfΔ}
    ( e: new = new' :> nat) :
    [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ] -> in_Fctx Δ new b -> [Δ ||-v σ  ≅ σ' : Γ,, new ↦ b | validFSnoc VΓ e | wfΔ].
  Proof.
    revert σ σ'.
    induction Γ, Γ', VΓ using validity_rect; intros σ σ' [] hin.
    + constructor.
      now eapply Fwk_new.
    + econstructor.
      now eapply irrLR.
      Unshelve.
      now unshelve now eapply irrelevanceSubst, IHVΓ.
  Qed.

  Lemma FSnocSubst {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) :
  forall {σ σ' Δ new b} (wfΔ : [|- Δ]) (wfΔnew : [|- Δ,, new ↦ b]),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ,,new ↦ b ||-v σ ≅ σ' : Γ | VΓ | wfΔnew ].
  Proof.
    intros ???????. revert σ σ'.
    induction Γ, Γ', VΓ using validity_rect; intros ?? [].
    + constructor.
      now eapply Fwk_Fstep.
    + unshelve econstructor.
      now eapply IHVΓ.
      eapply (irrLREq (A:= A[↑ >> σ]⟨wk_Fstep new b wk_id⟩)).
      etransitivity; [eapply wk_Fstep_ren_on | eapply wk_id_ren_on].
      rewrite <- (wk_id_ren_on Δ (σ var_zero)), <- (wk_id_ren_on Δ (σ' var_zero)),
        <- 2(wk_Fstep_ren_on new b).
      eapply wkLR, eqHead.
      Unshelve.
      now eapply wfc_consF.
  Qed.

  Lemma validFSnocSubst_notin {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b σ σ'} {Δ wfΔ}
    ( e: new = new' :> nat) (Vσσ' : [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ]) (notinΔ : not_in_Fctx Δ new) :
      let newΔ := Build_newnat Δ new notinΔ in [Δ,,newΔ ↦ b ||-v σ  ≅ σ' : Γ,, new ↦ b | validFSnoc VΓ e | wfc_consF wfΔ].
  Proof.
    intros ?.
    eapply validFSnocSubst_in.
    now eapply FSnocSubst.
    cbn.
    eapply in_hereF.
  Qed.

(*   Lemma validTy_shf {Γ} {wfΓ : [|-Γ]} {VΓ : [||-v Γ]} {l A B} :
    shf (fun Δ wfΔ ρ => forall (VΔ : [||-v Δ]), [Δ ||-v< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ]).
  Proof.
    intros ???? ht hf ?.
(*     set (new' := Build_newnat Δ' new (wk_new_notin new (lFwk (FequivValid VΔ)))). *)
    specialize (ht (validFSnoc VΔ eq_refl)).
    specialize (hf (validFSnoc VΔ eq_refl)).
    rewrite 2 !wk_Fstep_ren_on in ht,hf.
    constructor.
    intros Ξ wfΞ ???.
    destruct (decide_in Ξ new) as [ [] hin | hnotin].
    - eapply ht.
      eapply validFSnocSubst_in; tea.
    - eapply hf.
      eapply validFSnocSubst_in; tea.
    - eapply WAd_split.
      + eapply ht.
        now unshelve eapply validFSnocSubst_notin, vσσ'.
      + eapply hf.
        now unshelve eapply validFSnocSubst_notin, vσσ'.
  Qed.

  Lemma Split_bind_validTy {Γ} {wfΓ : [|-Γ]} {VΓ : [||-v Γ]} {l A B C } (hC : Split (wfΓ:=wfΓ) C) :
    (forall Δ (VΔ : [||-v Δ]) (ρ : Δ ≤ Γ), overtree hC Δ -> [Δ ||-v< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ]) ->
    [Γ ||-v< l > A ≅ B | VΓ].
  Proof.
    intros hAB.
    rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ B).
    unshelve eapply (Split_bind_alg validTy_shf hC), wfΓ; tea.
    intros ??? ohC ?.
    now eapply hAB.
  Qed. *)
End FSnoc.

Section Split.
Context `{GenericTypingProperties}.

Lemma validTySplit {Γ l A B} {new}
  {VΓ : [||-v Γ]} {VΓt : [||-v Γ,,new ↦ true]} {VΓf : [||-v Γ,,new ↦ false]}:
  [Γ,,new ↦ true ||-v<l> A ≅ B| VΓt] ->
  [Γ,,new ↦ false  ||-v<l> A ≅ B| VΓf] ->
  [Γ ||-v<l> A ≅ B| VΓ].
Proof.
  intros VAt VAf.
  econstructor.
  intros Δ wfΔ σ σ' Vσσ'.
  destruct (decide_in Δ new) as [[] hin|hnotin].
  + now unshelve now eapply VAt, convSubst, validFSnocSubst_in.
  + now unshelve now eapply VAf, convSubst, validFSnocSubst_in.
  + eapply WAd_split.
    - now unshelve now eapply VAt, convSubst, validFSnocSubst_notin.
    - now unshelve now eapply VAf, convSubst, validFSnocSubst_notin.
Qed.


Lemma Wpack_split {Γ l A B t u new}
  {RAt : [Γ,, new ↦ true ||-< l > A ≅ B]} {RAf : [Γ,, new ↦ false ||-< l > A ≅ B]} :
  [Γ,, new ↦ true ||-< l > t ≅ u  : A | RAt] -> [Γ,, new ↦ false ||-< l > t ≅ u  : A | RAf] ->
  [Γ ||-< l > t ≅ u : A | WAd_split RAt RAf].
Proof.
  intros Rtt Rtf.
  assert (wftrue : [|-Γ,, new ↦ true]) by apply RAt.
  assert (wffalse : [|-Γ,, new ↦ false]) by apply RAf.
  assert (wfΓ : [|-Γ]) by now eapply wfc_split.
  epose proof (Split_shf Γ wfΓ wk_id new).
  cbn in X.
  eapply Split_hom_PSh.
  2: eapply X; clear X.
  + intros ??? ?.
    rewrite wk_comp_runit in X0.
    exact X0.
  + eapply (dSplit_bind_return Rtt).
    intros ??? oRAt oRtt osplit.
    rewrite <- 2!wk_comp_ren_on, 2!wk_Fstep_ren_on, 2!wk_id_ren_on.
    unshelve eapply SirrLREq, Rtt, oRtt; tea.
    now rewrite <- wk_comp_ren_on, wk_Fstep_ren_on, wk_id_ren_on.
  + eapply (dSplit_bind_return Rtf).
    intros ??? oRAt oRtf osplit.
    rewrite <- 2!wk_comp_ren_on, 2!wk_Fstep_ren_on, 2!wk_id_ren_on.
    unshelve eapply SirrLREq, Rtf, oRtf; tea.
    now rewrite <- wk_comp_ren_on, wk_Fstep_ren_on, wk_id_ren_on.
Qed.

Lemma validTmSplit {Γ l A t u} {new}
  {VΓ : [||-v Γ]} {VΓt : [||-v Γ,,new ↦ true]} {VΓf : [||-v Γ,,new ↦ false]}
  {VAt : [Γ,,new ↦ true ||-v<l> A | VΓt]} {VAf : [Γ,,new ↦ false ||-v<l> A| VΓf]}:
  [Γ,,new ↦ true ||-v<l> t ≅ u : A | VΓt | VAt] ->
  [Γ,,new ↦ false  ||-v<l> t ≅ u : A | VΓf | VAf] ->
  [Γ ||-v<l> t ≅ u : A | VΓ | validTySplit VAt VAf].
Proof.
  intros Vtt Vtf.
  econstructor.
  intros ?????.
  destruct (decide_in Δ new) as [[] hin|hnotin].
  + unshelve eapply irrLR, Vtt; tea.
    now unshelve now eapply convSubst, validFSnocSubst_in.
  + unshelve eapply irrLR, Vtf; tea.
    now unshelve now eapply convSubst, validFSnocSubst_in.
  + eapply irrLR, Wpack_split.
    - unshelve eapply Vtt.
      1: now eapply wfc_consF.
      now unshelve now eapply convSubst, validFSnocSubst_notin.
    - unshelve eapply Vtf.
      1: now eapply wfc_consF.
      now unshelve now eapply convSubst, validFSnocSubst_notin.
Qed.

Lemma validCtxSplit {Γ new} :
  [||-v Γ,,new ↦ true] -> [||-v Γ,,new ↦ false] -> [||-v Γ].
Proof.
  intros VΓt VΓf.
  induction Γ using Tctx_induction.
  + now eapply validEmpty.
  + rewrite <- cons_Fcons in VΓt, VΓf.
    destruct (invValidity VΓt) as (lt&At'&Γt'&VΓt'&VAt'&et&et').
    revert VΓt' VAt' et'; pattern Γt', At', et.
    eapply cons_eq_inversion; clear dependent At'; clear Γt'.
    intros; cbn in et'; subst.
    destruct (invValidity VΓf) as (lf&Af'&Γf'&VΓf'&VAf'&ef&ef').
    revert VΓf' VAf' ef'; pattern Γf', Af', ef.
    eapply cons_eq_inversion; clear dependent Af'; clear Γf'.
    intros; cbn in ef'; subst.
    now unshelve now eapply validSnoc, validTySplit; eapply embValidTyOne.
Qed.

  Section Strong.

  Context {Γ wfΓ l}
    (NN : [Γ ||-Nat tNat ≅ tNat])
    (RN := LRNat_ l NN)
    (RB := boolRed (Γ:=Γ) (l:=l) wfΓ).

Lemma ty_nSucc {n t} :
  [Γ |- t : tNat] ->
  [Γ |- nSucc n t : tNat].
Proof.
  intros ht; induction n.
  - tea.
  - cbn. now eapply ty_succ.
Qed.

Lemma convtm_nSucc {n t t'} :
  [Γ |- t ≅ t': tNat] ->
  [Γ |- nSucc n t ≅ nSucc n t': tNat].
Proof.
  intros ht; induction n.
  - tea.
  - cbn. now eapply convtm_succ.
Qed.

Lemma nat_to_termReq n : NatPropEq Γ (nat_to_term n) (nat_to_term n).
Proof.
  induction n.
  - constructor.
  - cbn; constructor.
    econstructor.
    4: eapply IHn.
    1,2: now constructor; [| eapply redtm_refl]; eapply ty_nSucc, ty_zero.
    now eapply convtm_nSucc, convtm_zero.
Qed.

Lemma nSuccReq n {t t'} : [Γ||-Nat t ≅ t':Nat] -> [Γ ||-Nat nSucc n t ≅ nSucc n t' :Nat].
Proof.
  intros Rt.
  induction n.
  - eassumption.
  - cbn. unshelve eapply SsuccRed, IHn.
    4: eapply NN.
    tea.
Qed.

Lemma nSuccswap n t : nSucc n (tSucc t) = tSucc (nSucc n t).
Proof.
  induction n.
  + reflexivity.
  + cbn. now rewrite IHn.
Qed.

Inductive NatPropEqInst : term -> term -> Set :=
  | natReqInst n : NatPropEqInst (nat_to_term n) (nat_to_term n)
  | neReqInst n neL neR : [Γ ||-NeNf neL ≅ neR : tNat] ->
      NatPropEqInst (nSucc n neL) (nSucc n neR).

Record NatRedTmEqInst tL tR : Set :=
  {
    nfLInst : term ;
    nfRInst : term ;
    redLInst : forall n, [Γ |- tAlpha (nSucc n tL) :⤳*: tAlpha (nSucc n nfLInst) : tBool] ;
    redRInst : forall n, [Γ |- tAlpha (nSucc n tR) :⤳*: tAlpha (nSucc n nfRInst) : tBool ] ;
(*     eqInst : [Γ |- nfL ≅ nfR : tBool] ; *)
    propInst : NatPropEqInst nfLInst nfRInst
  }.


Lemma redtmwf_alphaSubst {t u n} :
  [ Γ |- t :⤳*: u : tNat ] ->
  [ Γ |- tAlpha (nSucc n t) :⤳*: tAlpha (nSucc n u) : tBool ].
Proof.
  intros ht.
  econstructor.
  + eapply ty_alpha, ty_nSucc, ht.
  + eapply redtm_alphaSubst, ht.
Qed.

Definition natRed_toInst :
  (forall tL tR (Rt : [Γ ||-Nat tL ≅ tR :Nat]), NatRedTmEqInst tL tR) ×
  (forall tL tR (propt : NatPropEq Γ tL tR), NatRedTmEqInst tL tR).
Proof.
  apply NatRedEqInduction.
  + intros tL tR ???? _ _ [dnfL dnfR redL' redR' prop].
    econstructor.
    3: eapply prop.
    all: now etransitivity; [eapply redtmwf_alphaSubst |].
  + econstructor.
    3: eapply (natReqInst 0).
    all: now intros n; eapply redtmwf_refl; eapply ty_alpha, ty_nSucc, ty_zero.
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
    1,2: intros; eapply redtmwf_refl, ty_alpha, ty_nSucc, Rne.
    now eapply (neReqInst 0).
Defined.


Lemma SAlphaRedEq (tL tR: term):
  [Γ ||-S< l > tL ≅ tR: tNat | SnatRed (l:=l) wfΓ] -> [Γ ||-< l > tAlpha tL ≅ tAlpha tR: tBool|boolRed (l:=l) wfΓ].
Proof.
  intros.
  eapply natRed_toInst in X.
  destruct X as [dnfL dnfR redL redR prop].
  induction prop.
  + specialize (redL 0); specialize (redR 0); cbn in redL, redR.
    destruct redL, redR.
    eapply redSubstTmEq; tea.
    destruct (decide_in Γ n) as [b hin | hnotin].
    - eapply redSubstTmEq.
      2,3: now eapply redtm_alpha.
      destruct b.
      eapply trueRed.
      eapply falseRed.
    - set (new := Build_newnat _ n hnotin).
      eassert (wfΓt :[ |-[ ta ] Γ,, new ↦ true])
         by now eapply wfc_consF.
      eassert (wfΓf :[ |-[ ta ] Γ,, new ↦ false])
         by now eapply wfc_consF.
      eapply irrLR, (Wpack_split (new:=new)).
      * eapply redSubstTmEq.
        2,3: now eapply redtm_alpha, in_hereF.
        now unshelve eapply trueRed.
      * eapply redSubstTmEq.
        2,3: now eapply redtm_alpha, in_hereF; eapply wfc_consF.
        now unshelve eapply falseRed.
      Unshelve. tea.
  + specialize (redL 0); specialize (redR 0); cbn in redL, redR.
    destruct redL, redR.
    eapply redSubstTmEq; tea.
    eapply neNfTermEq; econstructor; tea.
    eapply convneu_alpha, r.
Qed.

End Strong.


Lemma AlphaRedEq {Γ : context} {wfΓ : [|-Γ]} {l} (n n': term):
  [Γ ||-< l > n ≅ n': tNat | natRed (l:=l) wfΓ] -> [Γ ||-< l > tAlpha n ≅ tAlpha n': tBool|boolRed (l:=l) wfΓ].
Proof.
  intros Rnn'.
  eapply (dSplit_bind Rnn').
  intros ??? onatRed oRnn'.
  eapply Wpackrefold.
  change (tAlpha ?n)⟨?ρ⟩ with (tAlpha n⟨ρ⟩).
  eapply irrLR, SAlphaRedEq.
  now unshelve now eapply SirrLR, Rnn'.
  Unshelve. all:tea.
Qed.

Lemma validAlpha (Γ : context) (VΓ : [||-v Γ ≅ Γ])  (n n': term) l:
  [Γ ||-v< l > n ≅ n': tNat | VΓ| natValid VΓ] -> [Γ ||-v< l > tAlpha n ≅ tAlpha n': tBool |VΓ|boolValid VΓ].
Proof.
  intros Vn.
  econstructor.
  intros.
  instValid Vσσ'.
  change (tAlpha ?n)[?σ] with (tAlpha n[σ]).
  now eapply irrLR, AlphaRedEq.
Qed.

Lemma digammaRedEq (Γ : context) (n : nat) (b : bool) (wfΓ :[ |- Γ]) l:
  in_Fctx Γ n b ->  [Γ ||-<l> tAlpha (nat_to_term n) ≅ bool_to_term b : tBool | boolRed (l:=l) wfΓ].
Proof.
  intros hin.
  eapply redSubstLeftTmEq.
  2: now eapply redtm_alpha, hin.
  destruct b.
  eapply trueRed.
  eapply falseRed.
Qed.

Lemma nSucc_subst n t σ : (nSucc n t)[σ] = nSucc n (t[σ]).
Proof.
  induction n.
  + reflexivity.
  + cbn. now f_equal.
Qed.

Lemma nat_to_term_subst n σ : (nat_to_term n)[σ] = nat_to_term n.
Proof. eapply nSucc_subst. Qed.

Lemma bool_to_term_subst b σ : (bool_to_term b)[σ] = bool_to_term b.
Proof. induction b; reflexivity. Qed.

Inductive Box (P : SProp) : Type := box (p : P) : Box P.

Lemma validSubst_ε  {Γ Γ' σ σ' Δ} (VΓ : [||-v Γ ≅ Γ' ]) (wfΔ : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> Δ ≤ε Γ.
Proof.
  intros. enough (Box (Δ ≤ε Γ)) as [] by tea.
  revert σ σ' X.
  indValid VΓ.
  + intros * [].
    now constructor.
  + intros *.
    intros IH σ σ' [].
    eapply IH, eqTail.
Qed.

Lemma validDigamma  (Γ : context) (VΓ : [||-v Γ ≅ Γ])  (n : nat) (b:bool) l:
  in_Fctx Γ n b -> [Γ ||-v< l > tAlpha (nat_to_term n) ≅ bool_to_term b : tBool |VΓ|boolValid VΓ].
Proof.
  intros hin.
  econstructor.
  intros.
  change (tAlpha ?n)[?σ] with (tAlpha n[σ]).
  rewrite nat_to_term_subst, bool_to_term_subst.
  eapply irrLR, digammaRedEq.
  eapply validSubst_ε in Vσσ'.
  now eapply Vσσ'.
  Unshelve. all: tea.
Qed.

End Split.


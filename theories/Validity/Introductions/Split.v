From Stdlib Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Nat Bool SimpleArr Ell.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics Nat Bool Lambda.

Section FSnoc.
  Context `{GenericTypingProperties}.

  Lemma FequivValid {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) i i' : index_to_nat i = index_to_nat i' -> list_at Γ i =ε list_at Γ' i'.
  Proof.
    intros eqi.
    induction Γ, Γ', VΓ using validity_rect; tea.
    + destruct i.
    + destruct i, i'; cbn in eqi; inversion eqi.
      - eapply VF.
      - now eapply IHVΓ.
    + now eapply IHVΓ.
    + now eapply IHVΓ.
  Qed.

(*   Lemma FSnocValidTy {Γ} {new} A . *)

  Lemma validFSnoc {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {i i'} {new : newnat (list_at Γ i)} {new' : newnat (list_at Γ' i')} {b}:
    i = i' :> nat -> new = new' :> nat -> [||-v Γ,, i : new ↦ b ≅ Γ',, i' : new' ↦ b].
  Proof.
    intros eqi eqnew.
    induction Γ, Γ', VΓ using validity_rect.
    + destruct i.
    + destruct i, i'; cbn in *; [|inversion eqi..|].
      - eapply validSnocε; tea.
        destruct VF.
        now f_equal; eapply new_eq_is_nat_eq.
      - eapply validSnocε; tea.
        now eapply IHVΓ.
    + change [||-v Γ,, i : new ↦ b,,A ≅ Γ',, i' : new' ↦ b,,A'].
      unshelve eapply validSnoc; [shelve|easy|].
      constructor.
      intros * h.
      eapply (wkValidTy (wk_Fstep (i :list_index Γ)
        (new : newnat (list_at Γ i)) b wk_id)) in VA.
      rewrite 2!wk_Fstep_ren_on,  2!wk_id_ren_on in VA.
      eapply VA, h.
    + change [||-v Γ,, i : new ↦ b,,ℓ ≅ Γ',, i' : new' ↦ b,,ℓ'].
      unshelve eapply validSnocℓ; [shelve| easy |].
      constructor.
      intros * h.
      unshelve (eapply wkValidEll; tea).
      eapply wk_Fstep, wk_id.
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

  Lemma validFSnocSubst_in {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) i i' {new : newnat (list_at Γ i)} {new' : newnat (list_at Γ' i')} {b σ σ'} {Δ wfΔ}
    j (eqj :(index_to_nat j) =  σ.(subst_alpha) i) (eqi : i = i' :>nat) (eqnew: new = new' :> nat) :
    [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ] -> in_ell (list_at Δ j) new b -> [Δ ||-v σ  ≅ σ' : Γ,, i : new ↦ b | validFSnoc VΓ eqi eqnew | wfΔ].
  Proof.
    revert σ σ' eqj.
    induction Γ, Γ', VΓ using validity_rect; intros σ σ' eqj [] hin.
    + destruct i.
    + destruct i, i'; cbn in *; [ |inversion eqi..  ].
      - econstructor; tea; cbn.
        eapply Fwk_new; tea.
        rewrite <- eqj in εeqHeadIn.
        eapply index_to_nat_inj in εeqHeadIn.
        now destruct εeqHeadIn.
      - econstructor; tea.
        unshelve (eapply irrelevanceSubst, IHVΓ; tea); tea.
    + unshelve econstructor.
      now unshelve now eapply irrelevanceSubst, IHVΓ.
      now eapply irrLR.
    + unshelve econstructor.
      now unshelve now eapply irrelevanceSubst, IHVΓ.
      now eapply irrEll.
  Qed.


  Lemma ren_index_wk_Fstep {Γ Δ} {ρ : Δ ≤ Γ} {i new b j} : ren_index ρ j = ren_index (wk_Fstep i new b ρ) j :> nat.
  Proof.
    revert i new b j.
    induction ρ using wk_induction.
    + intros. destruct j.
    + intros.
      eapply IHρ.
    + intros. eapply IHρ.
    + intros.
      destruct i.
      - cbn. reflexivity.
      - cbn. erewrite IHρ. reflexivity.
    + intros.
      destruct i.
      - reflexivity.
      - destruct j.
        * cbn. reflexivity.
        * cbn. erewrite IHρ. reflexivity.
  Qed.

  Lemma ren_index_wk_id L (i : list_index L) : i = index_to_nat (ren_index well_Fwk_id i) :> nat.
  Proof.
    induction L; destruct i.
    + reflexivity.
    + cbn. now rewrite IHL.
  Qed.

  Lemma ren_index_Fwk1 {Δ} {i new b j}: index_to_nat j =
    index_to_nat (ren_index (well_Fwk (wk_Fstep i new b (@wk_id Δ))) j).
  Proof. now rewrite <- ren_index_wk_Fstep, ren_index_wk_id. Qed.


  Lemma FSnocSubst {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) :
  forall {σ σ' Δ i new b} (wfΔ : [|- Δ]) (wfΔnew : [|- Δ,, i : new ↦ b]),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ,, i : new ↦ b ||-v σ ≅ σ' : Γ | VΓ | wfΔnew ].
  Proof.
    intros ????????. revert σ σ'.
    induction Γ, Γ', VΓ using validity_rect; intros ?? Vσσ'.
    + constructor.
    + destruct Vσσ' as [htl j hd hj hin].
      unshelve econstructor; tea.
      exact (ren_index (wk_Fstep i new b wk_id) j).
      now eapply IHVΓ.
      * now rewrite <- ren_index_Fwk1.
      * intros n' b' hin'. eapply well_Fwk_in, hin, hin'.
    + destruct Vσσ' as [htl hhd].
      unshelve opector.
      now eapply IHVΓ.
      eapply (irrLREq (A:= A[tail_subst σ]⟨wk_Fstep i new b wk_id⟩)).
      etransitivity; [eapply wk_Fstep_ren_on | eapply wk_id_ren_on].
      rewrite <- (wk_id_ren_on Δ (subst_subst σ var_zero)), <- (wk_id_ren_on Δ (subst_subst σ' var_zero)),
        <- 2(wk_Fstep_ren_on i new b).
      eapply wkLR, hhd.
      Unshelve.
      now eapply wfc_consF.
    + destruct Vσσ' as [htl hhd].
      unshelve opector.
      now eapply IHVΓ.
      rewrite <- (wk_id_ren_on Δ (subst_subst σ var_zero)), <- (wk_id_ren_on Δ (subst_subst σ' var_zero)),
        <- 2(wk_Fstep_ren_on i new b).
      unshelve eapply irrEll, wkEll, irrEll, hhd.
      1,2: tea.
      now eapply wfc_consF.
  Qed.

  Lemma in_Fcons {L i new b i'} : index_to_nat i = index_to_nat i' :>nat ->
    in_ell (list_at (Fcons L i new b) i') new b.
  Proof.
    intros eqi.
    induction L as [|F L]; destruct i, i';  [|inversion eqi..|].
    + cbn. eapply in_cons_ell. repeat constructor.
    + eapply IHL. cbn in eqi.
      now inversion eqi.
  Qed.

  Lemma validFSnocSubst_notin {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {b σ σ'} {Δ wfΔ}
    i i' j {new : newnat (list_at Γ i)} {new' : newnat (list_at Γ' i')}
    (eqi : i = i' :> nat) (eqj : index_to_nat j = subst_alpha σ i :> nat) (eqnew: new = new' :> nat)
      (Vσσ' : [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ]) (notinΔ : notin_ell (list_at Δ j) new) :
      let newΔ := Build_newnat _ new notinΔ in
      [Δ,, j : newΔ ↦ b ||-v σ  ≅ σ' : Γ,, i : new ↦ b | validFSnoc VΓ eqi eqnew | wfc_consF wfΔ].
  Proof.
    intros ?.
    unshelve eapply validFSnocSubst_in.
    { exact (ren_index (wk_Fstep j newΔ b wk_id) j). }
    + now rewrite <- ren_index_Fwk1.
    + now eapply FSnocSubst.
    + exact (in_Fcons ren_index_Fwk1).
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

Lemma subst_index {Γ Γ'} {VΓ : [||-v Γ ≅ Γ']} {Δ wfΔ σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ ≅ Γ' | wfΔ]) (i : list_index Γ) :
  ∑ (j : list_index Δ), j = subst_alpha σ i :> nat × j = subst_alpha σ' i :> nat.
Proof.
  revert σ σ' Vσσ'; induction Γ, Γ', VΓ using validity_rect; intros σ σ' Vσσ'.
  + destruct i.
  + destruct i.
    - destruct Vσσ' as [htl j hd hj hin].
      exists j. split.
      * now symmetry.
      * etransitivity; tea; now symmetry.
    - destruct Vσσ' as [htl j hd hj hin].
      eapply IHVΓ with (1:=htl).
  + destruct Vσσ' as [htl hhd].
    eapply IHVΓ with (1:=htl).
  + destruct Vσσ' as [htl hhd].
    eapply IHVΓ with (1:=htl).
Qed.

Lemma validTySplit {Γ l A B} {i new}
  {VΓ : [||-v Γ]} {VΓt : [||-v Γ,, i : new ↦ true]} {VΓf : [||-v Γ,, i : new ↦ false]}:
  [Γ,, i : new ↦ true ||-v<l> A ≅ B| VΓt] ->
  [Γ,, i : new ↦ false  ||-v<l> A ≅ B| VΓf] ->
  [Γ ||-v<l> A ≅ B| VΓ].
Proof.
  intros VAt VAf.
  econstructor.
  intros Δ wfΔ σ σ' Vσσ'.
  destruct (subst_index Vσσ' i) as (j&eqj&eqj').
  destruct (decide_in (list_at Δ j) new) as [[] hin|hnotin].
  + now unshelve now eapply VAt, convSubst, validFSnocSubst_in.
  + now unshelve now eapply VAf, convSubst, validFSnocSubst_in.
  + eapply WAd_split; tea.
    - now unshelve now eapply VAt, convSubst, validFSnocSubst_notin.
    - now unshelve now eapply VAf, convSubst, validFSnocSubst_notin.
Qed.


Lemma Wpack_split {Γ wfΓ l A B t u i new}
  {RAt : [Γ,, i : new ↦ true ||-< l > A ≅ B]} {RAf : [Γ,, i : new ↦ false ||-< l > A ≅ B]} :
  [Γ,, i : new ↦ true ||-< l > t ≅ u  : A | RAt] -> [Γ,, i : new ↦ false ||-< l > t ≅ u  : A | RAf] ->
  [Γ ||-< l > t ≅ u : A | WAd_split wfΓ RAt RAf].
Proof.
  intros Rtt Rtf.
  assert (wftrue : [|-Γ,, i : new ↦ true]) by apply RAt.
  assert (wffalse : [|-Γ,, i : new ↦ false]) by apply RAf.
  epose proof (Split_shf Γ wfΓ wk_id i new).
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

Lemma validTmSplit {Γ l A t u} {i new}
  {VΓ : [||-v Γ]} {VΓt : [||-v Γ,, i : new ↦ true]} {VΓf : [||-v Γ,, i : new ↦ false]}
  {VAt : [Γ,, i : new ↦ true ||-v<l> A | VΓt]} {VAf : [Γ,, i : new ↦ false ||-v<l> A| VΓf]}:
  [Γ,, i : new ↦ true ||-v<l> t ≅ u : A | VΓt | VAt] ->
  [Γ,, i : new ↦ false  ||-v<l> t ≅ u : A | VΓf | VAf] ->
  [Γ ||-v<l> t ≅ u : A | VΓ | validTySplit VAt VAf].
Proof.
  intros Vtt Vtf.
  econstructor.
  intros ?????.
  destruct (subst_index Vσσ' i) as (j&eqj&eqj').
  destruct (decide_in (list_at Δ j) new) as [[] hin|hnotin].
  + unshelve eapply irrLR, Vtt; tea.
    now unshelve now eapply convSubst, validFSnocSubst_in.
  + unshelve eapply irrLR, Vtf; tea.
    now unshelve now eapply convSubst, validFSnocSubst_in.
  + eapply irrLR, (Wpack_split (wfΓ:=wfΔ)).
    - unshelve eapply Vtt.
      1: now eapply wfc_consF.
      now unshelve now eapply convSubst, validFSnocSubst_notin.
    - unshelve eapply Vtf.
      1: now eapply wfc_consF.
      now unshelve now eapply convSubst, validFSnocSubst_notin.
Qed.

(* Lemma validCtxSplit {Γ i new} :
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
Qed. *)

  Section Strong.

  Context {Γ wfΓ l}
    (NN : [Γ ||-Nat tNat ≅ tNat])
    (RN := LRNat_ l NN)
    (RB := boolRed (Γ:=Γ) (l:=l) wfΓ).

(* 
Inductive NatPropEqInst : term -> term -> Set :=
  | natReqInst n : NatPropEqInst (nat_to_term n) (nat_to_term n)
  | neReqInst n neL neR : [Γ ||-NeNf neL ≅ neR : tNat] ->
      NatPropEqInst (nSucc n neL) (nSucc n neR).

Record NatRedTmEqInst i tL tR : Set :=
  {
    nfLInst : term ;
    nfRInst : term ;
    redLInst : forall n, [Γ |- tApp (tAlpha i) (nSucc n tL) :⤳*: tApp (tAlpha i) (nSucc n nfLInst) : tBool] ;
    redRInst : forall n, [Γ |- tApp (tAlpha i) (nSucc n tR) :⤳*: tApp (tAlpha i) (nSucc n nfRInst) : tBool ] ;
(*     eqInst : [Γ |- nfL ≅ nfR : tBool] ; *)
    propInst : NatPropEqInst nfLInst nfRInst
  }. *)


Lemma redtmwf_alphaSubst {i : list_index Γ} {t u n} :
  [ Γ |- t :⤳*: u : tNat ] ->
  [ Γ |- tApp (tAlpha i) (nSucc n t) :⤳*: tApp (tAlpha i) (nSucc n u) : tBool ].
Proof.
  intros ht.
  econstructor.
  + eapply ty_simple_app, ty_nSucc, ht ; gtyping.
  + eapply redtm_alphaSubst, ht.
Qed.

Lemma SAppAlphaRedEqAux {i : list_index Γ} :
  (forall (tL tR: term), [Γ ||-Nat tL ≅ tR :Nat] ->
  forall n, [Γ ||-< l > tApp (tAlpha i) (nSucc n tL) ≅ tApp (tAlpha i) (nSucc n tR) : tBool|boolRed (l:=l) wfΓ]) ×
  (forall (tL tR: term), NatPropEq Γ tL tR ->
  forall n, [Γ ||-< l > tApp (tAlpha i) (nSucc n tL) ≅ tApp (tAlpha i) (nSucc n tR) : tBool|boolRed (l:=l) wfΓ]).
Proof.
  eapply NatRedEqInduction.
  + intros tL tR ?????? ihprop n.
    eapply redSubstTmEq.
    2,3: now eapply redtmwf_alphaSubst.
    eapply ihprop.
  + intros n.
    destruct (decide_in (list_at Γ i) n) as [b hin | hnotin].
    - eapply redSubstTmEq.
      2,3 : now eapply redtm_alpha.
      eapply bool_to_termRed.
    - set (new := Build_newnat _ n hnotin).
      eassert (wfΓt :[ |-[ ta ] Γ,, i : new ↦ true])
         by now eapply wfc_consF.
      eassert (wfΓf :[ |-[ ta ] Γ,, i : new ↦ false])
         by now eapply wfc_consF.
      eapply irrLR, (Wpack_split (new:=new)).
      * replace (tAlpha i) with (tAlpha (ren_index (wk_Fstep i new true wk_id) i))
          by now rewrite <- ren_index_Fwk1.
        eapply redSubstTmEq.
        2,3: eapply redtm_alpha; tea; refine (in_Fcons ren_index_Fwk1).
        now unshelve eapply trueRed.
      * replace (tAlpha i) with (tAlpha (ren_index (wk_Fstep i new false wk_id) i))
          by now rewrite <- ren_index_Fwk1.
        eapply redSubstTmEq.
        2,3: eapply redtm_alpha; tea; refine (in_Fcons ren_index_Fwk1).
        now unshelve eapply falseRed.
     Unshelve. all: tea.
  + intros tL tR Nt ihNt n.
    rewrite 2 nSuccswap.
    eapply (ihNt (S n)).
  + intros neL neR Rne n.
    eapply neNfTermEq; econstructor; tea.
    1,2 : eapply (ty_app (B:=tBool)), ty_nSucc, Rne;
      now eapply ty_alpha.
    eapply convneu_alpha, Rne.
Qed.

Lemma SAppAlphaRedEq (i : list_index Γ) (tL tR: term):
  [Γ ||-S< l > tL ≅ tR: tNat | SnatRed (l:=l) wfΓ] ->
  forall n, [Γ ||-< l > tApp (tAlpha i) (nSucc n tL) ≅ tApp (tAlpha i) (nSucc n tR) : tBool|boolRed (l:=l) wfΓ].
Proof. eapply SAppAlphaRedEqAux. Qed.


End Strong.


Lemma AppAlphaRedEq {Γ : context} {wfΓ : [|-Γ]} {l} {i : list_index Γ} (tL tR : term) n (RN : [Γ ||-< l> tNat ≅ tNat]):
  [Γ ||-< l > tL ≅ tR : tNat | RN] -> [Γ ||-< l > tApp (tAlpha i) (nSucc n tL) ≅ tApp (tAlpha i) (nSucc n tR) : tBool|boolRed (l:=l) wfΓ].
Proof.
  intros Rnn'.
  eapply (dSplit_bind Rnn').
  intros ??? oN oRnn'.
  eapply Wpackrefold.
  rewrite <-2 wk_app, <- wk_alpha, 2 wk_nSucc,
   <- ren_index_to_ren with (wρε := ρ).
  eapply irrLR, SAppAlphaRedEq.
  now unshelve now eapply SirrLR, Rnn'.
  Unshelve. all:tea.
Qed.


Lemma SAlphaRedEq {Γ : context} {wfΓ : [|-Γ]} {l} {i : list_index Γ} :
  [Γ ||-S< l > tAlpha i ≅ tAlpha i : arr' Γ tNat tBool| SNtoBRed (l:=l) wfΓ].
Proof.
  eapply canonPi_inv. cbn.
  assert (HN : [Γ |- tNat]) by eapply wft_term, ty_nat, wfΓ.
  assert (wfΓN : [|-Γ,,tNat]) by now eapply wfc_cons.
  assert ([Γ |- tProd tNat tBool ≅ tProd tNat tBool]).
  { eapply convty_prod; tea; eapply convty_term.
    * now eapply convtm_nat.
    * now eapply convtm_bool. }
  unshelve econstructor.
  + exists (tAlpha i); cbn.
    { eapply redtmwf_refl, ty_alpha, wfΓ. }
    now constructor.
  + exists (tAlpha i); cbn.
    { eapply redtmwf_refl, ty_alpha, wfΓ. }
    now constructor.
  + cbn. now eapply convtm_alpha.
  + intros Δ n n' ρ wfΔ Rnn'. cbn[PiRedTmEq.nf].
    apply Wpack_return in Rnn' as WRnn'.
    apply (@AppAlphaRedEq _ wfΔ _ (ren_index ρ i) n n' 0) in WRnn'.
    apply (dSplit_bind_return WRnn').
    intros Ξ wfΞ ρΞ oRB oWRnn' oirr.
    change (tAlpha i)⟨?ρ⟩ with (tAlpha (ρ.(Fwk) i)).
    rewrite <- (ren_index_to_ren ρ).
    unshelve eapply SirrLR, WRnn'; tea.
Qed.


Lemma AlphaRedEq {Γ : context} {wfΓ : [|-Γ]} {l} {i : list_index Γ} {A} (RNB : [Γ ||-< l > arr' Γ tNat tBool ≅ A]):
  [Γ ||-< l > tAlpha i ≅ tAlpha i : arr' Γ tNat tBool|RNB].
Proof. now unshelve now eapply irrLREq, Wpack_return, SAlphaRedEq. Qed.

Lemma validAppAlpha (Γ : context) (VΓ : [||-v Γ ≅ Γ]) {i : list_index Γ} (n n': term) l:
  [Γ ||-v< l > n ≅ n': tNat | VΓ| natValid VΓ] -> [Γ ||-v< l > tApp (tAlpha i) n ≅ tApp (tAlpha i) n': tBool |VΓ|boolValid VΓ].
Proof.
  intros Vn.
  econstructor.
  intros.
  instValid Vσσ'.
  change (tApp (tAlpha i) ?n)[?σ] with (tApp (tAlpha (subst_alpha σ i)) n[σ]).
  destruct (subst_index Vσσ' i) as (j&eqj&eqj').
  rewrite <- eqj, <- eqj'.
  now unshelve now eapply irrLR, AppAlphaRedEq with (n:=0).
Qed.

Lemma validAlpha (Γ : context) (VΓ : [||-v Γ ≅ Γ]) {i : list_index Γ} l (VNB : [Γ ||-v< l > arr' Γ tNat tBool | VΓ]):
  [Γ ||-v< l > tAlpha i : arr' Γ tNat tBool |VΓ|VNB].
Proof.
  constructor.
  intros.
  destruct (subst_index Vσσ' i) as (j&eqj&eqj').
  change (tAlpha i)[?σ] with (tAlpha (subst_alpha σ i)).
  rewrite <- eqj, <- eqj'.
  now unshelve eapply AlphaRedEq.
Qed.

Lemma digammaRedEq (Γ : context) {i : list_index Γ} (n : nat) (b : bool) (wfΓ :[ |- Γ]) l:
  in_ell (list_at Γ i) n b ->  [Γ ||-<l> tApp (tAlpha i) (nat_to_term n) ≅ bool_to_term b : tBool | boolRed (l:=l) wfΓ].
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

Lemma validSubst_ε  {Γ Γ' σ σ' Δ} (VΓ : [||-v Γ ≅ Γ' ]) (wfΔ : [|- Δ]) i j:
  index_to_nat j = subst_alpha σ (index_to_nat i) ->
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> list_at Δ j ≤ε list_at Γ i.
Proof.
  intros eqj Vσσ'. enough (Box (list_at (Fctx Δ) j ≤ε list_at (Fctx Γ) i)) as [] by tea.
  revert σ σ' i j eqj Vσσ'.
  indValid VΓ.
  + intros. destruct i.
  + intros * IHVΓ * ??.
    destruct i.
    * cbn. destruct Vσσ' as [htl j' hhd hj' hin].
      cbn in eqj; rewrite <- eqj in hj'.
      eapply index_to_nat_inj in hj'; destruct hj'.
      now constructor.
    * now eapply IHVΓ, Vσσ'.
  + intros * IHVΓ * ??.
    destruct Vσσ' as [htl hhd].
    now eapply IHVΓ, htl.
  + intros * IHVΓ * ??.
    destruct Vσσ' as [htl hhd].
    now eapply IHVΓ, htl.
Qed.

Lemma validDigamma (Γ : context) {i : list_index Γ}  (VΓ : [||-v Γ ≅ Γ]) (n : nat) (b:bool) l:
  in_ell (list_at Γ i) n b -> [Γ ||-v< l > tApp (tAlpha i) (nat_to_term n) ≅ bool_to_term b : tBool |VΓ|boolValid VΓ].
Proof.
  intros hin.
  econstructor.
  intros.
  change (tAlpha ?n)[?σ] with (tAlpha n[σ]).
  change (tApp (tAlpha i) ?n)[?σ] with (tApp (tAlpha (subst_alpha σ i)) n[σ]).
  destruct (subst_index Vσσ' i) as (j&eqj&eqj').
  rewrite <- eqj.
  rewrite nat_to_term_subst, bool_to_term_subst.
  eapply irrLR, digammaRedEq.
  eapply validSubst_ε in Vσσ'; tea.
  now eapply Vσσ'.
  Unshelve. all: tea.
Qed.

End Split.


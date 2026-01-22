
From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma natRedTy {Γ} : [|- Γ] -> [Γ ||-Nat tNat ≅ tNat].
Proof.
  constructor; eapply redtywf_refl; gen_typing.
Qed.

Definition SnatRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-S<l> tNat] :=
  LRNat_ l (natRedTy wfΓ).

Definition natRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-<l> tNat] :=
  WAd_return (SnatRed wfΓ).


Lemma natURedTm {Δ} (wfΔ : [|-Δ]) : URedTm zero Δ tNat.
Proof.
  exists tNat; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma natTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tNat : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve econstructor; try now eapply natURedTm.
  1: cbn; gtyping.
  eapply redTyRecBwd; now eapply SnatRed.
Defined.

Lemma SzeroRed {Γ l A B} {NN : [Γ ||-Nat A ≅ B]} : [Γ ||-<l> tZero : _ | LRNat_ l NN].
Proof.
  assert [|-Γ] by (pose (LRNat_ l NN); escape; gtyping).
  exists tZero tZero.
  1-3: gtyping.
  constructor.
Defined.

Lemma zeroRed {Γ l} (wfΓ : [|-Γ]) : [Γ ||-<l> tZero : _ | natRed (l:=l) wfΓ].
Proof.
  unshelve eapply Wpack_return, SirrLR, SzeroRed; tea.
  2: now eapply natRedTy.
Qed.

Lemma SsuccRed {Γ l A A' n n'} {NN : [Γ ||-Nat A ≅ A']} :
  [Γ ||-S<l> n ≅ n' : _ | LRNat_ l NN] ->
  [Γ ||-S<l> tSucc n ≅ tSucc n' : _ | LRNat_ l NN].
Proof.
  intros h; pose proof (h' :=h); inversion h'; subst.
  escape; exists (tSucc n) (tSucc n').
  1,2: eapply redtmwf_refl; eapply ty_succ; gen_typing.
  + eapply convtm_succ; eapply convtm_exp; gen_typing.
  + now constructor.
Defined.


Lemma succRed {Γ l n n'} (wfΓ : [|-Γ]) :
  [Γ ||-<l> n ≅ n' : _ | natRed (l:=l) wfΓ] ->
  [Γ ||-<l> tSucc n ≅ tSucc n' : _ | natRed (l:=l) wfΓ].
Proof.
  intros Rn.
  eapply (Split_bind_return Rn).
  intros Δ wfΔ ρ oRn oirr; cbn.
  unshelve (now eapply SirrLR, SsuccRed, SirrLR, Rn).
  3: eapply natRedTy.
  all: tea.
Qed.

Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  erewrite liftSubstComm'.
  now rewrite up_liftSubst_eq.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section SNatElimRedEq.
  Context {Γ l P Q hs hs' hz hz'}
    (NN : [Γ ||-Nat tNat ≅ tNat])
    (RN := LRNat_ _ NN)
    (WtP : [Γ ,, tNat |- P])
    (WtQ : [Γ ,, tNat |- Q])
    (eqPQ : [Γ,, tNat |- P ≅ Q])
    (RPQext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ Q[n'..]])
    (RPQz := RPQext _ _ SzeroRed)
    (Rhz : [Γ ||-<l> hz ≅ hz' : _ | RPQz])
    (RPQs : [Γ ||-<l> elimSuccHypTy P ≅ elimSuccHypTy Q])
    (Rhs : [Γ ||-<l> hs ≅ hs' : _ | RPQs ]) .

  Let RPext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Lemma SnatElimRedEqAux :
    (forall n n' (Rnn' : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPQext _ _ Rnn' ]) ×
    (forall n n' (Rnn' : NatPropEq Γ n n') (RP : [Γ ||-<l> P[n..] ≅ Q[n'..]]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RP ]).
  Proof.
    eassert ([|-Γ]) as wfΓ by (escape; gtyping).
    apply NatRedEqInduction.
    - intros t u  nfL nfR redL redR ? prop ih.
      set (Rtu := Build_NatRedTmEq _ _ _ _ _ _ : [Γ ||-S<l> t ≅ u : _ | RN]).
      pose proof (redTmFwd' Rtu) as []; eapply redSubstTmEq.
      + unshelve eapply irrLRConv, ih;
        first [eapply RPQext| eapply RPext]; tea; now symmetry.
      + escape; eapply redtm_natelim; tea; gen_typing.
      + escape; eapply redtm_natelim; tea; [..| gtyping].
        1,2: now eapply ty_conv.
    - intros; eapply redSubstTmEq.
      + eapply irrLR, Rhz.
      + escape; eapply redtm_natElimZero; tea.
      + escape; eapply redtm_natElimZero; tea.
        1,2: now eapply ty_conv.
    - intros n n' Rn ih ?; change [Γ ||-S<l> n ≅ n' : _ | RN] in Rn.
      eapply redSubstTmEq; cycle 1.
      + escape; eapply redtm_natElimSucc; tea.
      + escape; eapply redtm_natElimSucc; tea.
        1,2: now eapply ty_conv.
      + assert [Γ ||-<l> arr P[n..] P[(tSucc n)..] ≅ arr Q[n'..] Q[(tSucc n')..]].
        1: now eapply ArrRedTy; eapply RPQext;[|eapply SsuccRed].
        unshelve eapply simple_appcongTerm; [..| eauto]; tea.
        eapply Wpack_return in Rn as WRn.
        unshelve (eapply irrLREq, appcongTerm; tea;
          now rewrite subst_arr, liftSubst_singleSubst_eq); tea.
        now rewrite 2!subst_arr, 2!liftSubst_singleSubst_eq.
    - intros n n' Rn RP0.
      epose proof (SneNfTermEq RN Rn).
      escape.
      eapply irrLR.
      eapply neNfTermEq; constructor.
      + now eapply ty_natElim.
      + eapply ty_conv.
        eapply ty_natElim; tea.
        * now eapply ty_conv.
        * now eapply ty_conv.
        * now symmetry.
      + destruct Rn; now eapply convneu_natElim.
      Unshelve.
      2: now eapply lrefl.
  Qed.

  Lemma SnatElimRedEq :
    (forall n n' (Rnn' : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ |  (RPQext _ _ Rnn') ]).
  Proof. intros; now apply (fst SnatElimRedEqAux). Qed.
End SNatElimRedEq.

Section NatElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (WtP : [Γ ,, tNat |- P])
    (WtQ : [Γ ,, tNat |- Q])
    (eqPQ : [Γ,, tNat |- P ≅ Q])
    (RPQext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) n n' (Rn : [Δ ||-<l> n ≅ n' : _ | natRed (l:=l) wfΔ ]),
      [Δ ||-<l> P⟨wk_up tNat ρ⟩[n..] ≅ Q⟨wk_up tNat ρ⟩[n'..]]).


  Let RPQextnow : forall n n',
    [Γ ||-<l> n ≅ n' : _ | natRed (Γ := Γ) (l:=l) wfΓ] -> [Γ ||-<l> P[n..] ≅ Q[n'..]].
  Proof.
    intros n n' Rnn'.
    epose (RPQ := RPQext Γ wfΓ wk_id n n' Rnn').
    replace P with P⟨wk_id (Γ:=Γ,,tNat)⟩ by eapply wk_id_ren_on.
    now replace Q with Q⟨wk_id (Γ:=Γ,,tNat)⟩ by eapply wk_id_ren_on.
  Qed.

  Context {hs hs' hz hz'}
    (RPQz := RPQextnow _ _ (zeroRed wfΓ))
    (Rhz : [Γ ||-<l> hz ≅ hz' : _ | RPQz])
    (RPQs : [Γ ||-<l> elimSuccHypTy P ≅ elimSuccHypTy Q])
    (Rhs : [Γ ||-<l> hs ≅ hs' : _ | RPQs ]).

  Let RPext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) n n' (Rn : [Δ ||-<l> n ≅ n' : _ | natRed (l:=l) wfΔ]),
      [Δ ||-<l> P⟨wk_up tNat ρ⟩[n..] ≅ P⟨wk_up tNat ρ⟩[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.


  Lemma natElimRedEq n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | natRed wfΓ]):
      [Γ ||-<l> tNatElim P hz hs n ≅ tNatElim Q hz' hs' n' : _ | RPQextnow _ _ Rnn' ].
  Proof.
    eapply (dSplit_bind Rnn').
    intros Δ wfΔ ρ oRN oRnn'.
    eapply Wpackrefold.
    eassert [|-Δ,,tNat] as wfΔN by (eapply wfc_cons; gtyping).
    rewrite <- 2wk_natElim.
    eapply irrLREq, SnatElimRedEq; refold.
    1: symmetry; eapply subst_ren_wk_up.
    Unshelve.
    + now eapply wft_wk.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + unshelve eapply irrLREq, wkLRTm, Rhz; tea.
      exact (subst_ren_wk_up _).
    + unshelve eapply irrLREq, wkLRTm, Rhs; tea.
      symmetry; eapply wk_elimSuccHypTy.
    + easy.
    + now eapply natRedTy.
    + clear dependent n; clear n'; intros n n' Rnn'.
      eapply (RPQext _ wfΔ), Wpack_return, SirrLR, Rnn'.
    + now unshelve now eapply SirrLREq, Rnn'.
    + rewrite 2 wk_elimSuccHypTy.
      now eapply wkLRTy.
  Qed.

End NatElimRedEq.

End Nat.

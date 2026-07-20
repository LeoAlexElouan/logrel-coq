
From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.
From Equations Require Import Equations.

Section Bool.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma boolRedTy {Γ} : [|- Γ] -> [Γ ||-Bool tBool ≅ tBool].
Proof.
  constructor; eapply redtywf_refl; gen_typing.
Qed.

Definition SboolRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-S<l> tBool] :=
  LRBool_ l (boolRedTy wfΓ).

Definition boolRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-<l> tBool] :=
  WAd_return (SboolRed wfΓ).


Lemma boolURedTm {Δ} (wfΔ : [|-Δ]) : URedTm zero Δ tBool.
Proof.
  exists tBool; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma boolTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tBool : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve econstructor; try now eapply boolURedTm.
  1: cbn; gtyping.
  eapply redTyRecBwd; now eapply SboolRed.
Defined.

Lemma StrueRed {Γ l A B} {NN : [Γ ||-Bool A ≅ B]} : [Γ ||-<l> tTrue : _ | LRBool_ l NN].
Proof.
  assert [|-Γ] by (pose (LRBool_ l NN); escape; gtyping).
  exists tTrue tTrue.
  1-3: gtyping.
  constructor.
Defined.

Lemma trueRed {Γ l} (wfΓ : [|-Γ]) : [Γ ||-<l> tTrue : _ | boolRed (l:=l) wfΓ].
Proof.
  eapply Wpack_return, SirrLR, StrueRed.
  Unshelve.
  3: eapply boolRedTy.
  all: tea.
Qed.

Lemma SfalseRed {Γ l A B} {NN : [Γ ||-Bool A ≅ B]} : [Γ ||-<l> tFalse : _ | LRBool_ l NN].
Proof.
  assert [|-Γ] by (pose (LRBool_ l NN); escape; gtyping).
  exists tFalse tFalse.
  1-3: gtyping.
  constructor.
Defined.

Lemma falseRed {Γ l} (wfΓ : [|-Γ]) : [Γ ||-<l> tFalse : _ | boolRed (l:=l) wfΓ].
Proof.
  eapply Wpack_return, SirrLR, SfalseRed.
  Unshelve.
  3: eapply boolRedTy.
  all: tea.
Qed.

Lemma Sbool_to_termRed {Γ l A B b} {NN : [Γ ||-Bool A ≅ B]} : [Γ ||-S<l> bool_to_term b : _ | LRBool_ l NN].
Proof.
  destruct b.
  - eapply StrueRed.
  - eapply SfalseRed.
Qed.

Lemma bool_to_termRed {Γ l b} (wfΓ : [|-Γ]) : [Γ ||-<l> bool_to_term b : _ | boolRed (l:=l) wfΓ].
Proof.
  destruct b.
  - eapply trueRed.
  - eapply falseRed.
Qed.

Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section SBoolElimRedEq.
  Context {Γ l P Q ht ht' hf hf'}
    (NN : [Γ ||-Bool tBool ≅ tBool])
    (RN := LRBool_ _ NN)
    (WtP : [Γ ,, tBool |- P])
    (WtQ : [Γ ,, tBool |- Q])
    (eqPQ : [Γ,, tBool |- P ≅ Q])
    (RPQext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ Q[n'..]])
    (RPQt := RPQext _ _ StrueRed)
    (RPQf := RPQext _ _ SfalseRed)
    (Rht : [Γ ||-<l> ht ≅ ht' : _ | RPQt])
    (Rhf : [Γ ||-<l> hf ≅ hf' : _ | RPQf]).

  Let RPext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Lemma SboolElimRedEqAux :
    forall n n' (Rnn' : BoolPropEq Γ n n') (RP : [Γ ||-<l> P[n..] ≅ Q[n'..]]),
      [Γ ||-<l> tBoolElim P ht hf n ≅ tBoolElim Q ht' hf' n' : _ | RP ].
  Proof.
    intros ???.
    destruct Rnn'.
    - intros; eapply redSubstTmEq.
      + eapply irrLR, Rht.
      + escape; eapply redtm_boolElimTrue; tea.
      + escape; eapply redtm_boolElimTrue; tea.
        1,2: now eapply ty_conv.
    - intros; eapply redSubstTmEq.
      + eapply irrLR, Rhf.
      + escape; eapply redtm_boolElimFalse; tea.
      + escape; eapply redtm_boolElimFalse; tea.
        1,2: now eapply ty_conv.
    - intros RP.
      pose proof (SneNfTermEq RN r).
      escape.
      eapply irrLR.
      eapply neNfTermEq; constructor.
      + now eapply ty_boolElim.
      + eapply ty_conv.
        eapply ty_boolElim; tea.
        * now eapply ty_conv.
        * now eapply ty_conv.
        * now symmetry.
      + destruct r; now eapply convneu_boolElim.
      Unshelve.
      2: now eapply lrefl.
  Qed.

  Lemma SboolElimRedEq :
    (forall n n' (Rnn' : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> tBoolElim P ht hf n ≅ tBoolElim Q ht' hf' n' : _  | RPQext _ _ Rnn' ]).
  Proof.
    intros ???.
    pose proof (redTmFwd' Rnn') as [].
    depelim Rnn'; eapply redSubstTmEq; cycle 1.
    + escape; eapply redtm_boolelim; tea; gen_typing.
    + escape; eapply redtm_boolelim; tea; gen_typing.
    + unshelve eapply irrLRConv, SboolElimRedEqAux, prop;
        first [eapply RPQext| eapply RPext]; tea; now symmetry.
  Qed.

End SBoolElimRedEq.

Section BoolElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (WtP : [Γ ,, tBool |- P])
    (WtQ : [Γ ,, tBool |- Q])
    (eqPQ : [Γ,, tBool |- P ≅ Q])
    (RPQext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) n n' (Rn : [Δ ||-<l> n ≅ n' : _ | boolRed (l:=l) wfΔ ]),
      [Δ ||-<l> P⟨wk_up tBool ρ⟩[n..] ≅ Q⟨wk_up tBool ρ⟩[n'..]]).


  Let RPQextnow : forall n n',
    [Γ ||-<l> n ≅ n' : _ | boolRed (Γ := Γ) (l:=l) wfΓ] -> [Γ ||-<l> P[n..] ≅ Q[n'..]].
  Proof.
    intros n n' Rnn'.
    epose (RPQ := RPQext Γ wfΓ wk_id n n' Rnn').
    replace P with P⟨wk_id (Γ:=Γ,,tBool)⟩ by eapply wk_id_ren_on.
    now replace Q with Q⟨wk_id (Γ:=Γ,,tBool)⟩ by eapply wk_id_ren_on.
  Qed.

  Context {ht ht' hf hf'}
    (RPQt := RPQextnow _ _ (trueRed wfΓ))
    (RPQf := RPQextnow _ _ (falseRed wfΓ))
    (Rht : [Γ ||-<l> ht ≅ ht' : _ | RPQt])
    (Rhf : [Γ ||-<l> hf ≅ hf' : _ | RPQf]).

  Let RPext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) n n' (Rn : [Δ ||-<l> n ≅ n' : _ | boolRed (l:=l) wfΔ]),
      [Δ ||-<l> P⟨wk_up tBool ρ⟩[n..] ≅ P⟨wk_up tBool ρ⟩[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.


  Lemma boolElimRedEq n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | boolRed wfΓ]):
      [Γ ||-<l> tBoolElim P ht hf n ≅ tBoolElim Q ht' hf' n' : _ | RPQextnow _ _ Rnn' ].
  Proof.
    eapply (dSplit_bind Rnn').
    intros Δ wfΔ ρ oRN oRnn'.
    eapply Wpackrefold.
    eassert [|-Δ,,tBool] as wfΔB by (eapply wfc_cons; gtyping).
    rewrite <- 2wk_boolElim.
    eapply irrLREq, SboolElimRedEq; refold.
    1: symmetry; eapply subst_ren_wk_up.
    Unshelve.
    + now eapply wft_wk.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + unshelve eapply irrLREq, wkLRTm, Rht; tea.
      exact (subst_ren_wk_up _).
    + unshelve eapply irrLREq, wkLRTm, Rhf; tea.
      exact (subst_ren_wk_up _).
    + easy.
    + now eapply boolRedTy.
    + clear dependent n; clear n'; intros n n' Rnn'.
      eapply (RPQext _ wfΔ), Wpack_return, SirrLR, Rnn'.
    + now unshelve now eapply SirrLREq, Rnn'.
  Qed.

End BoolElimRedEq.






End Bool.

From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application.
From Equations Require Import Equations.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Empty.
Context `{GenericTypingProperties}.


Lemma emptyRedTy {Γ} : [|- Γ] -> [Γ ||-Empty tEmpty ≅ tEmpty].
Proof. intros; constructor; eapply redtywf_refl; gen_typing. Defined.

Lemma SemptyRed {Γ l} : [|- Γ] -> [Γ ||-S<l> tEmpty].
Proof. intros; now apply LREmpty_, emptyRedTy. Defined.

Lemma emptyRed {Γ l} : [|- Γ] -> [Γ ||-<l> tEmpty].
Proof. intros wfΓ. now eapply WAd_return, SemptyRed. Defined.

Lemma emptyURedTm {Δ l} (wfΔ : [|-Δ]) : URedTm l Δ tEmpty.
Proof.
  exists tEmpty; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma emptyTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tEmpty : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve eexists (emptyURedTm wfΔ) (emptyURedTm wfΔ); cbn.
  1: gtyping.
  now eapply (SemptyRed (l:=zero)).
Defined.




Section SEmptyElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (NN : [Γ ||-Empty tEmpty ≅ tEmpty])
    (RN := LREmpty_ l NN)
    (WtP : [Γ,, tEmpty |- P])
    (WtQ : [Γ,, tEmpty |- Q])
    (eqPQ : [Γ,, tEmpty |- P ≅ Q])
    (RPQext : forall n n', [Γ ||-S<l> n ≅ n' : _ | RN] -> [Γ ||-<l> P[n..] ≅ Q[n'..]]).

  Let RPext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-<l> P[n..] ≅ P[n'..] ].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.


  Lemma SemptyElimRedEq n n' (Rnn' : [Γ ||-S<l> n ≅ n' : _ | RN])
    (RPQ : [Γ ||-<l> P[n..] ≅ Q[n'..]]):
    [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPQ ].
  Proof.
    pose proof (redTmFwd' Rnn') as [].
    depelim Rnn' ; eapply redSubstTmEq; cycle 1.
    + eapply redtm_emptyelim; tea; gen_typing.
    + eapply redtm_emptyelim; tea; gen_typing.
    + cbn -[Wpack] in e,e0,e1.
     destruct eq; eapply irrLRConv.
      (* gtyping/gen_typing not working well here... *)
      2: eapply neNfTermEq; constructor; [now eapply ty_emptyElim |..].
      - eapply RPext; now symmetry.
      - eapply ty_conv; [now eapply ty_emptyElim|].
        symmetry; now eapply escapeSplitTy, RPQext.
      - now eapply convneu_emptyElim.
      Unshelve. now eapply lrefl, RPQext.
  Qed.
End SEmptyElimRedEq.



Section EmptyElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (WtP : [Γ,, tEmpty |- P])
    (WtQ : [Γ,, tEmpty |- Q])
    (eqPQ : [Γ,, tEmpty |- P ≅ Q])
    (RPQext : forall Δ wfΔ (ρ : Δ ≤Γ) n n',
      [Δ ||-<l> n ≅ n' : _ | emptyRed (Γ := Δ) (l:=l) wfΔ] -> [Δ ||-<l> P⟨wk_up tEmpty ρ⟩[n..] ≅ Q⟨wk_up tEmpty ρ⟩[n'..]]).

  Let RPext : forall Δ wfΔ (ρ : Δ ≤Γ) n n' (Rn : [Δ ||-<l> n ≅ n' : _ | emptyRed (Γ := Δ) (l:=l) wfΔ]),
      [Δ ||-<l> P⟨wk_up tEmpty ρ⟩[n..] ≅ P⟨wk_up tEmpty ρ⟩[n'..] ].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Let RPQextnow : forall n n', [Γ ||-<l> n ≅ n' : _ | emptyRed (Γ := Γ) (l:=l) wfΓ] -> [Γ ||-<l> P[n..] ≅ Q[n'..]].
  Proof.
    intros n n' Rnn'.
    epose (RPQ := RPQext Γ wfΓ wk_id n n' Rnn').
    replace P with P⟨wk_id (Γ:=Γ,,tEmpty)⟩ by eapply wk_id_ren_on.
    now replace Q with Q⟨wk_id (Γ:=Γ,,tEmpty)⟩ by eapply wk_id_ren_on.
  Qed.


  Lemma emptyElimRedEq n n' (Rnn' : [Γ ||-<l> n ≅ n' : _ | emptyRed wfΓ]) :
    [Γ ||-<l> tEmptyElim P n ≅ tEmptyElim Q n' : _ | RPQextnow _ _ Rnn' ].
  Proof.
    eapply (dSplit_bind Rnn').
    intros Δ wfΔ ρ oRN oRnn'.
    eapply Wpackrefold.
    eassert [|-Δ,,tEmpty] as wfΔE by (eapply wfc_cons; gtyping).
    rewrite <- 2wk_emptyElim.
    eapply irrLREq, SemptyElimRedEq; refold.
    1: symmetry; eapply subst_ren_wk_up.
    Unshelve.
    + now eapply wft_wk.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + clear dependent n; clear n'; intros n n' Rnn'.
      eapply (RPQext _ wfΔ), Wpack_return, SirrLR, Rnn'.
    + now unshelve now eapply SirrLREq, Rnn'.
    + easy.
    + now unshelve now eapply RPQext, irrLREq, wkLRTm, Rnn'.
    + now eapply emptyRedTy.
  Qed.
End EmptyElimRedEq.


End Empty.


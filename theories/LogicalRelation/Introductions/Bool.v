
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
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

Definition boolRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-S<l> tBool] :=
  LRBool_ l (boolRedTy wfΓ).


Lemma boolURedTm {Δ} (wfΔ : [|-Δ]) : URedTm zero Δ tBool.
Proof.
  exists tBool; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma boolTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tBool : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve econstructor; try now eapply boolURedTm.
  1: cbn; gtyping.
  eapply redTyRecBwd; now eapply boolRed.
Defined.

Lemma trueRed {Γ l A B} {NN : [Γ ||-Bool A ≅ B]} : [Γ ||-<l> tTrue : _ | LRBool_ l NN].
Proof.
  assert [|-Γ] by (pose (LRBool_ l NN); escape; gtyping).
  exists tTrue tTrue.
  1-3: gtyping.
  constructor.
Defined.

Lemma falseRed {Γ l A B} {NN : [Γ ||-Bool A ≅ B]} : [Γ ||-<l> tFalse : _ | LRBool_ l NN].
Proof.
  assert [|-Γ] by (pose (LRBool_ l NN); escape; gtyping).
  exists tFalse tFalse.
  1-3: gtyping.
  constructor.
Defined.


Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.

Section BoolElimRedEq.
  Context {Γ l P Q ht ht' hf hf'}
    (NN : [Γ ||-Bool tBool ≅ tBool])
    (RN := LRBool_ _ NN)
    (WtP : [Γ ,, tBool |- P])
    (WtQ : [Γ ,, tBool |- Q])
    (eqPQ : [Γ,, tBool |- P ≅ Q])
    (RPQext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-S<l> P[n..] ≅ Q[n'..]])
    (RPQt := RPQext _ _ trueRed)
    (RPQf := RPQext _ _ falseRed)
    (Rht : [Γ ||-S<l> ht ≅ ht' : _ | RPQt])
    (Rhf : [Γ ||-S<l> hf ≅ hf' : _ | RPQf]).

  #[local]
  Lemma RPext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-S<l> P[n..] ≅ P[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

  Lemma boolElimRedEqAux :
    forall n n' (Rnn' : BoolPropEq Γ n n') (RP : [Γ ||-S<l> P[n..] ≅ Q[n'..]]),
      [Γ ||-S<l> tBoolElim P ht hf n ≅ tBoolElim Q ht' hf' n' : _ | RP ].
  Proof.
    intros ???.
    destruct Rnn'.
    - intros; eapply SredSubstTmEq.
      + eapply SirrLR, Rht.
      + escape; eapply redtm_boolElimTrue; tea.
      + escape; eapply redtm_boolElimTrue; tea.
        1,2: now eapply ty_conv.
    - intros; eapply SredSubstTmEq.
      + eapply SirrLR, Rhf.
      + escape; eapply redtm_boolElimFalse; tea.
      + escape; eapply redtm_boolElimFalse; tea.
        1,2: now eapply ty_conv.
    - intros RP.
      pose proof (neNfTermEq RN r).
      eapply reflectLR.
      + escape; now eapply ty_boolElim.
      + eapply ty_conv ; [| eapply escapeEq; now symmetry].
        escape; eapply ty_boolElim; tea.
        all: now eapply ty_conv.
      + escape ; destruct r; now eapply convneu_boolElim.
  Qed.

  Lemma boolElimRedEq :
    (forall n n' (Rnn' : [Γ ||-S<l> n ≅ n' : _ | RN]),
      [Γ ||-S<l> tBoolElim P ht hf n ≅ tBoolElim Q ht' hf' n' : _  | RPQext _ _ Rnn' ]).
  Proof.
    intros ???.
    pose proof (redTmFwd' Rnn') as [].
    depelim Rnn'; eapply SredSubstTmEq; cycle 1.
    + escape; eapply redtm_boolelim; tea; gen_typing.
    + escape; eapply redtm_boolelim; tea; gen_typing.
    + unshelve eapply SirrLRConv, boolElimRedEqAux, prop;
        first [eapply RPQext| eapply RPext]; tea; now symmetry.
  Qed.

End BoolElimRedEq.



End Bool.

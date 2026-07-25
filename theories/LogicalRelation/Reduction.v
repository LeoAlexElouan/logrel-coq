From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Transitivity.

Set Universe Polymorphism.

Section Reduction.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma red_redtywf_trans {Γ A B C} : [Γ |- A ⤳* B] -> [Γ |- B :⤳*: C] -> [Γ |- A :⤳*: C].
Proof.
  intros ? []; constructor; tea; now etransitivity.
Qed.

Lemma red_redtmwf_trans {Γ t u v A B} : [Γ |- A ≅ B] -> [Γ |- t ⤳* u : A] -> [Γ |- u :⤳*: v : B] -> [Γ |- t :⤳*: v : B].
Proof.
  intros ?? []; constructor; tea; etransitivity; tea; now eapply redtm_conv.
Qed.

Lemma SredSubst {Γ A B B' l} :
  [Γ ||-S<l> B ≅ B'] ->
  [Γ |- A ⤳* B] ->
  [Γ ||-S<l> A ≅ B'].
Proof.
  intros lr; revert A; indLR lr.
  - intros [] **; apply LRU_.
    econstructor; tea; now eapply red_redtywf_trans.
  - intros [] **; apply LRne_.
    econstructor; tea; now eapply red_redtywf_trans.
  - intros [???? []] **; cbn in *; apply LRPi'.
    econstructor; tea; constructor; tea; now eapply red_redtywf_trans.
  - intros [] **; apply LRNat_.
    constructor; tea; now eapply red_redtywf_trans.
  - intros [] **; apply LRBool_.
    constructor; tea; now eapply red_redtywf_trans.
  - intros [] **; apply LREmpty_.
    constructor; tea; now eapply red_redtywf_trans.
  - intros [] **; apply LRTree_.
    constructor; tea; now eapply red_redtywf_trans.
  - intros [???? []] **; cbn in *; apply LRSig'.
    econstructor; tea; constructor; tea; now eapply red_redtywf_trans.
  - intros [] **; cbn in *; apply LRId'.
    econstructor; tea; now eapply red_redtywf_trans.
Qed.

Lemma redSubst {Γ} {A B B' l} :
  [Γ ||-<l> B ≅ B'] ->
  [Γ |- A ⤳* B] ->
  [Γ ||-<l> A ≅ B'].
Proof.
  intros lr hAB.
  eapply (Split_bind_return lr).
  intros Δ wfΔ ρ olr.
  eapply SredSubst, redty_wk, hAB; tea.
  now unshelve eapply lr.
Defined.

Lemma redwfSubst {Γ} {A B B' l} :
  [Γ ||-<l> B ≅ B'] ->
  [Γ |- A :⤳*: B] ->
  [Γ ||-<l> A ≅ B'].
Proof.
  intros ? []; now eapply redSubst.
Qed.


Lemma redURedTm {Γ l l' A B t u} {h : [Γ ||-U<l> A ≅ B]} :
  [Γ |- t ⤳* u : A] ->
  URedTm l' Γ u ->
  URedTm l' Γ t.
Proof.
  intros redtu ru; pose proof (whredL_conv (LRU_ h)).
  assert [Γ |- t : U] by (eapply ty_conv; [gen_typing| now escape]).
  destruct ru as [nf]; exists nf; tea.
  now eapply red_redtmwf_trans.
Defined.

Lemma redPiRedTm {Γ l A B t u} {h : [Γ ||-Π<l> A ≅ B]} :
  [Γ |- t ⤳* u : A] ->
  PiRedTm h u ->
  PiRedTm h t.
Proof.
  intros redtu ru; pose proof (whredL_conv (LRPi' h)).
  destruct ru as [nf]; exists nf; tea.
  now eapply red_redtmwf_trans.
Defined.

Lemma redSigRedTm {Γ l A B t u} {h : [Γ ||-Σ<l> A ≅ B]} :
  [Γ |- t ⤳* u : A] ->
  SigRedTm h u ->
  SigRedTm h t.
Proof.
  intros redtu ru; pose proof (whredL_conv (LRSig' h)).
  destruct ru as [nf]; exists nf; tea.
  now eapply red_redtmwf_trans.
Defined.

Lemma SredSubstLeftTmEq {Γ A B t u v l} (RA : [Γ ||-S<l> A ≅ B]) :
  [Γ ||-S<l> u ≅ v : A | RA] ->
  [Γ |- t ⤳* u : A ] ->
  [Γ ||-S<l> t ≅ v : A | RA].
Proof.
  intros Ruv redtu.
  pose proof (conv:= whredL_conv RA).
  revert t u v Ruv conv redtu ; indLR RA.
  - intros * [] **; unshelve econstructor; tea.
    1: (unshelve now eapply redURedTm); [| |tea].
    1: tea.
    assert (redtytu : [Γ |-[ ta ] t ⤳* u]) by (eapply redty_term; cbn in *; gtyping).
    eapply redTyRecBwd, SredSubst; tea; now eapply redTyRecFwd.
  - intros * [] **; econstructor; tea.
    now eapply red_redtmwf_trans.
  - intros * ?? * [] **; unshelve econstructor; tea.
    1: now eapply redPiRedTm.
    all: cbn; eauto.
  - intros * [] **; econstructor; tea.
    now eapply red_redtmwf_trans.
  - intros * [] **; econstructor; tea.
    now eapply red_redtmwf_trans.
  - intros * [] **; econstructor; tea.
    now eapply red_redtmwf_trans.
  - intros * Ruv;
    induction u, v, Ruv using TreeRedTmEq.TreeRedTmEq_destruct;
    intros **; econstructor; tea.
    now eapply red_redtmwf_trans.
  - intros * ?? * [] **; unshelve econstructor; tea.
    1: now eapply redSigRedTm.
    all: cbn; eauto.
  - intros * ? * [] **; unshelve econstructor.
    4: tea.
    2: now eapply red_redtmwf_trans.
    all: cbn; eauto.
Qed.

Lemma redSubstLeftTmEq {Γ A B t u v l} (RA : [Γ ||-<l> A ≅ B]) :
  [Γ ||-<l> u ≅ v : A | RA] ->
  [Γ |- t ⤳* u : A ] ->
  [Γ ||-<l> t ≅ v : A | RA].
Proof.
  intros huv hRtu.
  eapply (dSplit_bind_return huv).
  intros Δ wfΔ ρ _ ohuv oRA.
  eapply SredSubstLeftTmEq, redtm_wk, hRtu; tea.
  now eapply huv.
Qed.

Lemma SredSubstTmEq {Γ A A' tl tr ul ur l} (RA : [Γ ||-S<l> A ≅ A']) :
  [Γ ||-S<l> ul ≅ ur : A | RA] ->
  [Γ |- tl ⤳* ul : A ] ->
  [Γ |- tr ⤳* ur : A' ] ->
  [Γ ||-S<l> tl ≅ tr : A | RA].
Proof.
  intros.
  assert [Γ |- tr ⤳* ur : A ].
  1: eapply redtm_conv; tea; escape; now symmetry.
  eapply SredSubstLeftTmEq; tea; symmetry.
  eapply SredSubstLeftTmEq; tea; now symmetry.
Qed.

Lemma redSubstTmEq {Γ A A' tl tr ul ur l} (RA : [Γ ||-<l> A ≅ A']) :
  [Γ ||-<l> ul ≅ ur : A | RA] ->
  [Γ |- tl ⤳* ul : A ] ->
  [Γ |- tr ⤳* ur : A' ] ->
  [Γ ||-<l> tl ≅ tr : A | RA].
Proof.
  intros.
  assert [Γ |- tr ⤳* ur : A ].
  1: eapply redtm_conv; tea; escape; now symmetry.
  eapply redSubstLeftTmEq; tea; eapply Symmetry.symLR.
  eapply redSubstLeftTmEq; tea; now eapply Symmetry.symLR.
Qed.

Lemma SredSubstTmEq' {Γ A A' tl tr ul ur l} (RA : [Γ ||-S<l> A ≅ A']) :
  [Γ ||-S<l> ul ≅ ur : A | RA] ->
  [Γ |- tl ⤳* ul : A ] ->
  [Γ |- tr ⤳* ur : A' ] ->
  [Γ ||-S<l> tl ≅ tr : A | RA] × [Γ ||-S<l> tl ≅ ul : _ | LRAd.pack (lrefl RA)] × [Γ ||-S<l> tr ≅ ur : _ | LRAd.pack (urefl RA)].
Proof.
  intros; prod_splitter.
  + now eapply SredSubstTmEq.
  + eapply SredSubstLeftTmEq; tea. now eapply lrefl, SirrLR.
  + eapply SredSubstLeftTmEq; tea; now eapply urefl, SirrLRConv.
Qed.

Lemma redSubstTmEq' {Γ A A' tl tr ul ur l} (RA : [Γ ||-<l> A ≅ A']) :
  [Γ ||-<l> ul ≅ ur : A | RA] ->
  [Γ |- tl ⤳* ul : A ] ->
  [Γ |- tr ⤳* ur : A' ] ->
  [Γ ||-<l> tl ≅ tr : A | RA] × [Γ ||-<l> tl ≅ ul : _ | lrefl RA] × [Γ ||-<l> tr ≅ ur : _ | urefl RA].
Proof.
  intros; prod_splitter.
  + now eapply redSubstTmEq.
  + eapply redSubstLeftTmEq; tea. now eapply lreflRedTm, irrLR.
  + eapply redSubstLeftTmEq; tea; now eapply ureflRedTm, irrLRConv.
Qed.

Lemma redwfSubstTmEq {Γ A t u v l} (RA : [Γ ||-<l> A]) :
  [Γ ||-<l> u ≅ v : A | RA] ->
  [Γ |- t :⤳*: u : A ] ->
  [Γ ||-<l> t ≅ v : A | RA].
Proof.
  intros ? []; now eapply redSubstLeftTmEq.
Qed.

Lemma redFwd {Γ l A B} (lr : [Γ ||-S<l> A ≅ B]) :
  [Γ ||-S<l> (whredtyL lr).(tyred_whnf) ≅ (whredtyR lr).(tyred_whnf)].
Proof.
  indLR lr.
  - intros []; cbn in *; apply LRU_; econstructor; tea; gtyping.
  - intros []; cbn in *; apply LRne_; econstructor.
    1,2: eapply redtywf_refl; gtyping.
    tea.
  - intros [???? [] []] _ _; cbn in *; apply LRPi'; econstructor.
    1,2: econstructor; [eapply redtywf_refl|..]; tea; gtyping.
    all: tea.
  - intros []; cbn in *; apply LRNat_; econstructor; gtyping.
  - intros []; cbn in *; apply LRBool_; econstructor; gtyping.
  - intros []; cbn in *; apply LREmpty_; econstructor; gtyping.
  - intros []; cbn in *; apply LRTree_; econstructor; gtyping.
  - intros [???? [] []] _ _; cbn in *; apply LRSig'; econstructor.
    1,2: econstructor; [eapply redtywf_refl|..]; tea; gtyping.
    all: tea.
  - intros [] _; cbn in *; apply LRId'; econstructor.
    1,2: eapply redtywf_refl; gtyping.
    all: tea.
Qed.

(* Lemma redFwd {Γ l A B} (lr : [Γ ||-<l> A ≅ B]) :
  dSplit_wfc (fun Δ ρ lr => [Δ ||-<l> (whredtyL lr).(tyred_whnf)⟨ρ⟩ ≅ (whredtyR lr).(tyred_whnf)⟨ρ⟩]) lr.
 *)
Lemma redFwd' {Γ l A B} (lr : [Γ ||-S<l> A ≅ B]) :
  [Γ ||-S<l> A ≅ (whredtyL lr).(tyred_whnf)] × [Γ ||-S<l> B ≅ (whredtyR lr).(tyred_whnf)].
Proof.
  split.
  - eapply SredSubst; [eapply lrefl, redFwd|]; gtyping.
  - eapply SredSubst; [eapply urefl, redFwd|]; gtyping.
Qed.

Arguments IdRedTy.outTy {_ _ _ _ _ _ _ _ _ _ _ _ _ _} _ /.

Lemma redFwdURedTm {Γ l l' A B t} {h : [Γ ||-U<l> A ≅ B]}
  (Rt : URedTm l' Γ t) : URedTm l' Γ (URedTm.te Rt).
Proof.
  destruct Rt; econstructor; cbn; tea.
  eapply redtmwf_refl; gtyping.
Defined.

Lemma redFwdPiRedTm {Γ l A B t} {ΠA : [Γ ||-Π<l> A ≅ B]}
  (Rt : PiRedTm ΠA t) : PiRedTm ΠA (PiRedTmEq.nf Rt).
Proof.
  destruct Rt; econstructor; cbn; tea.
  cbn in *; eapply redtmwf_refl; gtyping.
Defined.

Lemma redFwdSigRedTm {Γ l A B t} {ΣA : [Γ ||-Σ<l> A ≅ B]}
  (Rt : SigRedTm ΣA t) : SigRedTm ΣA (SigRedTmEq.nf Rt).
Proof.
  destruct Rt; econstructor; cbn; tea.
  cbn in *; eapply redtmwf_refl; gtyping.
Defined.

Lemma redTmFwd {Γ l A B t u} {RA : [Γ ||-S<l> A ≅ B]}
  (Rtu : [Γ ||-S<l> t ≅ u : A | RA]) :
  [Γ ||-S<l> (whredtmL Rtu).(tmred_whnf) ≅ (whredtmR Rtu).(tmred_whnf) : _  | RA].
Proof.
  revert Rtu; caseLR RA; intros h Rtu;
  first [destruct Rtu| induction t, u, Rtu using TreeRedTmEq.TreeRedTmEq_destruct];
  cbn in *; unshelve econstructor.
  all: try match goal with
    | [|- URedTm _ _ _] => tea ; (unshelve now eapply redFwdURedTm) ; [| | | tea]
    | [|- PiRedTm _ _] => tea ; now eapply redFwdPiRedTm
    | [|- SigRedTm _ _] => tea; now eapply redFwdSigRedTm
    | [|- [_ |-[ _ ] _ :⤳*: _ : _]] => apply redtmwf_refl ; cbn; gtyping end.
  all: tea.
  pose proof (Rtu := redTyRecFwd _ relEq).
  pose proof (eql := whredtm_ty_det (whredtyL Rtu) (whredtm redL)).
  pose proof (eqr := whredtm_ty_det (whredtyR Rtu) (whredtm redR)).
  cbn in eql, eqr; rewrite <-eql, <-eqr.
  eapply redTyRecBwd, redFwd.
Qed.

Lemma redTmFwd' {Γ l A B t u} {RA : [Γ ||-S<l> A ≅ B]}
  (Rtu : [Γ ||-S<l> t ≅ u : A | RA]) :
  [× [Γ ||-S<l> t ≅ (whredtmL Rtu).(tmred_whnf) : _| RA],
    [Γ ||-S<l> (whredtmL Rtu).(tmred_whnf) ≅ (whredtmR Rtu).(tmred_whnf) : _  | RA],
    [Γ ||-S<l> (whredtmR Rtu).(tmred_whnf) ≅ u : _ | RA],
    [Γ ||-S<l> A ≅ (whredtyL RA).(tyred_whnf)] &
    [Γ ||-S<l> A ≅ (whredtyR RA).(tyred_whnf)] ].
Proof.
  pose proof (redTmFwd Rtu); pose proof (redFwd' RA) as [RAwh RBwh].
  split; tea.
  + eapply SredSubstLeftTmEq; [now eapply lrefl|].
    eapply redtm_conv; [|symmetry; now eapply escapeEq ].
    eapply tmred_whnf_red.
  + symmetry; eapply SredSubstLeftTmEq; [now eapply urefl|].
    eapply redtm_conv; [|symmetry; now eapply escapeEq ].
    eapply tmred_whnf_red.
  + etransitivity;[|tea]; tea.
Qed.

End Reduction.
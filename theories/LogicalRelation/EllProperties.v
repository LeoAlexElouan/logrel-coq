From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity Weakening Neutral Reduction InstKripke NormalRed.

Section EllProperties.
  Context `{GenericTypingProperties}.

  Lemma Sirrisell {Γ l l' ℓ ℓ' ℓ'' t}
    (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) (Rℓ' : [Γ ||-EllS< l' > ℓ ≅ ℓ'']) :
    EllRedTmEq.isLREll Rℓ t -> EllRedTmEq.isLREll Rℓ' t.
  Proof.
    intros isellt.
    destruct isellt as [t Rt Rtnb| ]; constructor; tea.
    now eapply SirrLR.
  Qed.

  Lemma SirrEll {Γ l l' ℓ ℓ' ℓ'' t t'}
    (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) (Rℓ' : [Γ ||-EllS< l' > ℓ ≅ ℓ'']) :
    [Γ ||-S< l > t ≅ t' : _ | Rℓ] -> [Γ ||-S< l' > t ≅ t' : _ | Rℓ'].
  Proof.
    intros [].
    constructor; tea.
    1,2: now eapply Sirrisell.
    now eapply SirrLR.
  Qed.
  Lemma irrEll {Γ l l' ℓ ℓ' ℓ'' t t'}
    (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) (Rℓ' : [Γ ||-Ell< l' > ℓ ≅ ℓ'']) :
    [Γ ||-< l > t ≅ t' : _ | Rℓ] -> [Γ ||-< l' > t ≅ t' : _ | Rℓ'].
  Proof.
    intros Rt.
    eapply (dSplit_bind_return Rt).
    intros ??? oRℓ oRt oRℓ'.
    now unshelve eapply SirrEll, Rt.
  Qed.


  Lemma SsymEll {Γ l ℓ ℓ'} :
    [Γ ||-EllS< l > ℓ ≅ ℓ'] -> [Γ ||-EllS< l > ℓ' ≅ ℓ].
  Proof. intros [? ->]; now constructor. Qed.
  Lemma symEll {Γ l ℓ ℓ'} :
    [Γ ||-Ell< l > ℓ ≅ ℓ'] -> [Γ ||-Ell< l > ℓ' ≅ ℓ].
  Proof.
    intros Rℓ.
    eapply (Split_bind_return Rℓ).
    intros ??? oRℓ.
    now eapply SsymEll, Rℓ.
  Qed.

  Lemma StransEll {Γ l l' ℓ ℓ' ℓ''} :
    [Γ ||-EllS< l > ℓ ≅ ℓ'] -> [Γ ||-EllS< l' > ℓ' ≅ ℓ''] -> [Γ ||-EllS< l > ℓ ≅ ℓ''].
  Proof. now intros Rℓ [? ->]. Qed.
  Lemma transEll {Γ l l' ℓ ℓ' ℓ''} :
    [Γ ||-Ell< l > ℓ ≅ ℓ'] -> [Γ ||-Ell< l' > ℓ' ≅ ℓ''] -> [Γ ||-Ell< l > ℓ ≅ ℓ''].
  Proof.
    intros Rℓ Rℓ'.
    eapply (Split_bind Rℓ).
    intros ??? oRℓ.
    unshelve eapply (Split_wk_bind_return Rℓ'); tea.
    intros ??? oRℓ'.
    eapply StransEll.
    + unshelve eapply Rℓ; tea.
      { exact (ρΞ ∘w ρ). }
      now eapply overtree_PSh.
    + now eapply Rℓ'.
  Qed.

  #[global]Instance SperEll Γ l : PER (EllAdequate Γ l).
  Proof.
    constructor.
    - intros ??; eapply SsymEll.
    - intros ???; eapply StransEll.
  Qed.
  #[global]Instance perEll Γ l : PER (WEllAdequate Γ l).
  Proof.
    constructor.
    - intros ??; eapply symEll.
    - intros ???; eapply transEll.
  Qed.

  Lemma SsymEllTm {Γ l ℓ ℓ' t t'} (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) :
    [Γ ||-S< l > t ≅ t' : _ | Rℓ ] -> [Γ ||-S< l > t' ≅ t : _ | Rℓ ].
  Proof.
    intros Rt.
    destruct Rt; constructor; tea.
    all: now symmetry.
  Qed.
  Lemma symEllTm {Γ l ℓ ℓ' t t'} (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) :
    [Γ ||-< l > t ≅ t' : _ | Rℓ ] -> [Γ ||-< l > t' ≅ t : _ | Rℓ ].
  Proof.
    intros Rt.
    eapply (dSplit_bind_return Rt).
    intros ??? _ oRt oRℓ.
    now eapply SsymEllTm, Rt.
  Qed.

  Lemma StransEllTm {Γ l ℓ ℓ' t t' t''} (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) :
    [Γ ||-S< l > t ≅ t' : _ | Rℓ ] -> [Γ ||-S< l > t' ≅ t'' : _ | Rℓ ] -> [Γ ||-S< l > t ≅ t'' : _ | Rℓ ].
  Proof.
    intros Rt Rt'.
    destruct Rt, Rt'; constructor; tea.
    1,2 : now etransitivity.
  Qed.
  Lemma transEllTm {Γ l ℓ ℓ' t t' t''} (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) :
    [Γ ||-< l > t ≅ t' : _ | Rℓ ] -> [Γ ||-< l > t' ≅ t'' : _ | Rℓ ] -> [Γ ||-< l > t ≅ t'' : _ | Rℓ ].
  Proof.
    intros Rt Rt'.
    eapply (dSplit_bind Rt).
    intros ??? _ oRt.
    unshelve eapply (dSplit_wk_bind_return Rt'); tea.
    intros ??? _ oRt' oRℓ.
    eapply StransEllTm.
    + now eapply Rt, overtree_PSh.
    + now eapply Rt'.
  Qed.

  #[global]Instance SperEllTm Γ l ℓ ℓ' (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) : PER (LRPack.eqTm (EllRedTmEq.EllPack Rℓ)).
  Proof.
    constructor.
    - intros ??; eapply SsymEllTm.
    - intros ???; eapply StransEllTm.
  Qed.
  #[global]Instance perEllTm Γ l ℓ ℓ' (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) : PER (LRPack.eqTm (WEllpack Rℓ)).
  Proof.
    constructor.
    - intros ??; eapply symEllTm.
    - intros ???; eapply transEllTm.
  Qed.

  Lemma escapeEll {Γ l ℓ ℓ' t t'} (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) :
    [Γ ||-S< l > t ≅ t' : _ | Rℓ ] -> [Γ |- t : ℓ] × [Γ |- t' : ℓ] × [Γ |- t ≅ t' : ℓ].
  Proof. intros []; prod_splitter; tea. Qed.
  Lemma escapeSplitEll {Γ l ℓ ℓ' t t'} (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) :
    [Γ ||-< l > t ≅ t' : _ | Rℓ ] -> [Γ |- t : ℓ] × [Γ |- t' : ℓ] × [Γ |- t ≅ t' : ℓ].
  Proof.
    intros Rt.
    prod_splitter.
    + eapply (dSplit_bind_ty Rt).
      intros ??? oRℓ oRt.
      now unshelve eapply fst, escapeEll, Rt.
    + eapply (dSplit_bind_ty Rt).
      intros ??? oRℓ oRt.
      now unshelve eapply escapeEll, Rt.
    + eapply (dSplit_bind_convtm Rt).
      intros ??? oRℓ oRt.
      now unshelve eapply escapeEll, Rt.
  Qed.

  Lemma wkisell {Γ Δ l ℓ ℓ' t} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) (Rℓ' : [Δ ||-EllS< l > ℓ ≅ ℓ']):
    EllRedTmEq.isLREll Rℓ t -> EllRedTmEq.isLREll Rℓ' t⟨ρ⟩.
  Proof.
    intros isellt.
    destruct isellt as [t Rt Rtnb |]; tea.
    + rewrite <- wk_box; constructor.
      { now unshelve eapply SirrLREq, SwkLR, Rt. }
      intros n b inℓ.
      erewrite <- wk_nat_to_term, <- wk_bool_to_term, wk_app.
      now eapply wkBoolTm.
    + constructor. now eapply in_ctx_wk with (d:=ℓ).
  Qed.


  Lemma SwkEll {Γ Δ l ℓ ℓ'} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    [Γ ||-EllS< l > ℓ ≅ ℓ'] -> [Δ ||-EllS< l > ℓ ≅ ℓ'].
  Proof.
    intros [? <-]; repeat constructor; tea.
    now unshelve  eapply (SwkLR _ _ _ NtoBAd).
  Qed.
  Lemma wkEll {Γ Δ l ℓ ℓ'} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) :
    [Γ ||-Ell< l > ℓ ≅ ℓ'] -> [Δ ||-Ell< l > ℓ ≅ ℓ'].
  Proof.
    intros Rℓ.
    unshelve eapply (Split_wk_bind_return Rℓ); tea.
    intros ??? oRℓ.
    now eapply Rℓ.
  Qed.

  Lemma SwkEllTm {Γ Δ l ℓ ℓ' t t'} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) (Rℓ' : [Δ ||-EllS< l > ℓ ≅ ℓ']):
    [Γ ||-S< l > t ≅ t' : _ | Rℓ] -> [Δ ||-S< l > t⟨ρ⟩ ≅ t'⟨ρ⟩ : _ | Rℓ'].
  Proof.
    intros Rtt'.
    destruct Rtt'; constructor; tea.
    1,2: now eapply wkisell.
    1,2: now eapply (ty_wk (A:=ℓ)).
    1: now eapply (convtm_wk (A:=ℓ)).
    rewrite ! wk_eval.
    now unshelve eapply SirrLREq, SwkLR, eqeval.
  Qed.
  Lemma wkEllTm {Γ Δ l ℓ ℓ' t t'} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) (Rℓ' : [Δ ||-Ell< l > ℓ ≅ ℓ']):
    [Γ ||-< l > t ≅ t' : _ | Rℓ] -> [Δ ||-< l > t⟨ρ⟩ ≅ t'⟨ρ⟩ : _ | Rℓ'].
  Proof.
    intros Rtt'.
    unshelve eapply (dSplit_wk_bind_return Rtt'); tea.
    intros ??? oRℓ oRtt' oRℓ'.
    rewrite ! wk_comp_ren_on.
    now unshelve eapply SirrEll, Rtt'.
  Qed.

  Lemma WEllpackrefold {Γ l ℓ ℓ' t t'} {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ)
    (Rℓ : [Γ ||-Ell< l > ℓ ≅ ℓ']) (Rℓ' := wkEll ρ wfΔ Rℓ) :
    [Δ ||-< l > t⟨ρ⟩ ≅ t'⟨ρ⟩ : _ | Rℓ'] ->
    Split (fun Ξ wfΞ ρΞ => forall oRℓ : overtree Rℓ (ρΞ ∘w ρ),
      [Ξ ||-S< l > t⟨ρΞ ∘w ρ⟩ ≅ t'⟨ρΞ ∘w ρ⟩ : _ | cover Rℓ Ξ wfΞ (ρΞ ∘w ρ) oRℓ]).
  Proof.
    intros Rt.
    eapply (dSplit_bind_return Rt).
    intros Ξ wfΞ ρΞ oRℓ' oRt oRℓ.
    rewrite <-! wk_comp_ren_on.
    now unshelve eapply SirrEll, Rt.
  Qed.

  Lemma SirrEllConv {Γ l ll lr ℓl ℓl' ℓr ℓr' t t'}
    (Rℓl : [Γ ||-Ell< ll > ℓl ≅ ℓl']) (Rℓr : [Γ ||-Ell< lr > ℓr ≅ ℓr']) 
    (Rℓ : [Γ ||-EllS< l > ℓl ≅ ℓr]):
    [Γ ||-< ll > t ≅ t' : _ | Rℓl] -> [Γ ||-< lr > t ≅ t' : _ | Rℓr].
  Proof.
    intros Rt.
    destruct Rℓ as [_ <-].
    now eapply irrEll.
  Qed.
  Lemma irrEllConv {Γ l ll lr ℓl ℓl' ℓr ℓr' t t'}
    (Rℓl : [Γ ||-Ell< ll > ℓl ≅ ℓl']) (Rℓr : [Γ ||-Ell< lr > ℓr ≅ ℓr']) 
    (Rℓ : [Γ ||-Ell< l > ℓl ≅ ℓr]):
    [Γ ||-< ll > t ≅ t' : _ | Rℓl] -> [Γ ||-< lr > t ≅ t' : _ | Rℓr].
  Proof.
    intros Rt.
    eapply (Split_bind Rℓ).
    intros ??? oRℓ.
    unshelve eapply WEllpackrefold; tea.
    unshelve (eapply SirrEllConv, wkEllTm, Rt; tea); [shelve|..].
    1: now eapply wkEll.
    now eapply Rℓ.
  Qed.


End EllProperties.

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-S< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-S< _ > _ ≅ _  : _ | LRAd.pack ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTm RA H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-<_> _ ≅ _  : _ | Wpack ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTm _ H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-S< _ > _ ≅ _  : _ | EllRedTmEq.EllPack ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeEll RA H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-< _ > _ ≅ _  : _ | WEllpack ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitEll RA H) as (Xl & Xr & X) );
      block H
  end; unblock.
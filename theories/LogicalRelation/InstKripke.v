(** * LogRel.LogicalRelation.InstKripke: combinators to instantiate Kripke-style quantifications *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity Weakening Neutral.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section InstKripke.
Context `{GenericTypingProperties}.

Lemma SinstKripkeTm {Γ A A' t u l} (wfΓ : [|-Γ])
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : _])
  : [SinstKripke wfΓ h | Γ ||- t ≅ u : _].
Proof.
  specialize (eq Γ wk_id wfΓ).
  eapply SirrLREq in eq; [|eapply wk_id_ren_on].
  erewrite 2!wk_id_ren_on in eq.
  eapply eq.
Qed.

Lemma instKripkeTm {Γ A A' t u l} (wfΓ : [|-Γ])
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [wfΔ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : _])
  : [instKripke wfΓ h | Γ ||- t ≅ u : _].
Proof.
  specialize (eq Γ wk_id wfΓ).
  eapply irrLREq in eq; [|eapply wk_id_ren_on].
  erewrite 2!wk_id_ren_on in eq.
  eapply eq.
Qed.

Lemma instKripkeFam {Γ} (wfΓ : [|-Γ]) {A} (wfA : [Γ |- A]) {A' B B' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ wfc_cons wfΓ wfA ||-<l> B ≅ B'].
Proof.
  pose proof (SinstKripke wfΓ hA) as RAA'.
  escape.
  unshelve epose proof (hinst := hB (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) (wfc_cons wfΓ wfA) _).
  1: eapply Svar0; tea; now bsimpl.
  now rewrite 2!var0_wk1_id in hinst.
Qed.


Lemma instKripkeFamTm {Γ} {wfΓ : [|-Γ]} {A} {wfA : [Γ |- A]} {A' B B' t u l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeFam wfΓ wfA hB |  Γ ,, A ||- t ≅ u : _].
Proof.
  pose proof (SinstKripke wfΓ hA).
  escape. set (wfΓA := wfc_cons wfΓ wfA).
  unshelve epose proof (hinst := eq (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply Svar0; tea; now bsimpl.
  eapply irrLREq in hinst.
  rewrite 2!var0_wk1_id in hinst; tea.
  eapply var0_wk1_id.
Qed.

Lemma instKripkeFamConv {Γ A A' B B' l} (wfΓ : [|-Γ]) (wfA' : [Γ |- A'])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  : [ wfc_cons wfΓ wfA' ||-<l> B ≅ B'].
Proof.
  unshelve eapply instKripkeFam.
  2: intros; symmetry; eauto.
  1: tea.
  unshelve (intros; eapply hB; now eapply SirrLRSym); tea.
Qed.




Lemma instKripkeFamConvTm {Γ A A' B B' t u l} (wfΓ : [|-Γ]) (wfA' : [Γ |- A'])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t[a .: ρ >> tRel] ≅ u[b .: ρ >> tRel] : _])
  : [ instKripkeFamConv wfΓ wfA' hB |  Γ ,, A' ||- t ≅ u : _].
Proof.
  eapply irrLR.
  unshelve eapply instKripkeFamTm.
  2: tea.
  2: intros; symmetry; eauto.
  1: unshelve (intros; eapply hB; now eapply SirrLRSym); tea.
  intros; unshelve eapply irrLR, eq; tea; now eapply SirrLRSym.
Qed.

Lemma instKripkeSubst {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  (RA : [Γ ||-S<l> A ≅ A'])
  [t t']
  (ht : [_ ||-S<l> t ≅ t' : _ | RA])
  : [ wfΓ ||-<l> B[t..] ≅ B'[t'..]].
Proof.
  erewrite 2!eq_subst_scons; unshelve eapply hB; tea.
  eapply SirrLREq; [eapply eq_sym, wk_id_ren_on|]; rewrite 2! wk_id_ren_on; eapply ht.
Qed.

Lemma instKripkeSubst' {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]])
  (RA : [wfΓ ||-<l> A ≅ A'])
  [t t']
  (ht : [_ ||-<l> t ≅ t' : _ | RA])
  : [ wfΓ ||-<l> B[t..] ≅ B'[t'..]].
Proof.
  eapply (dSplit_bind ht).
  intros ??? oRA oht.
  eapply WAdrefold.
  rewrite 2!subst_ren_subst_mixed.
  now unshelve eapply hB, SirrLR, ht.
Qed.

Lemma instKripkeSubstTm {Γ A A' B B' u u' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [wfΔ ||-<l> B[a .: ρ >> tRel] ≅ B'[b .: ρ >> tRel]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- u[a .: ρ >> tRel] ≅ u'[b .: ρ >> tRel] : _])
  (RA : [Γ ||-S<l> A ≅ A'])
  [t t' ]
  (ht : [_ ||-S<l> t ≅ t' : _ | RA])
  : [ _ ||-<l> u[t..] ≅ u'[t'..] : _ | instKripkeSubst wfΓ hB RA ht].
Proof.
  eapply irrLREq; [eapply eq_sym, eq_subst_scons|].
  erewrite 2!eq_subst_scons.
  unshelve eapply eq; tea.
  eapply SirrLREq; [eapply eq_sym, wk_id_ren_on|]; now rewrite 2!wk_id_ren_on.
Qed.

End InstKripke.



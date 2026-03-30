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
  {h : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (eq : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [h Δ ρ wfΔ | Δ ||- t⟨ρ⟩ ≅ u⟨ρ⟩ : _])
  : [instKripke wfΓ h | Γ ||- t ≅ u : _].
Proof.
  specialize (eq Γ wk_id wfΓ).
  eapply irrLREq in eq; [|eapply wk_id_ren_on].
  erewrite 2!wk_id_ren_on in eq.
  eapply eq.
Qed.

Lemma instKripkeFam {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  : [ Γ,,A ||-<l> B ≅ B'].
Proof.
  pose proof (SinstKripke wfΓ hA) as RAA'.
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := hB (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply Svar0; tea; now bsimpl.
  change B'⟨wk_up A' (wk1 A)⟩ with B'⟨wk_up (Γ := Γ,,A') A' (wk1 A')⟩ in hinst.
  now rewrite !wk1_eta in hinst.
Qed.


Lemma instKripkeFamTm {Γ A A' B B' t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t⟨wk_up A ρ⟩[a ..] ≅ u⟨wk_up A' ρ⟩[b ..] : _])
  : [ instKripkeFam wfΓ hB |  Γ ,, A ||- t ≅ u : _].
Proof.
  pose proof (SinstKripke wfΓ hA).
  escape. assert (wfΓA : [|- Γ ,, A]) by gen_typing.
  unshelve epose proof (hinst := eq (Γ ,, A) (tRel 0) (tRel 0) (@wk1 Γ A) wfΓA _).
  1: eapply Svar0; tea; now bsimpl.
  eapply irrLREq in hinst.
  change u⟨wk_up A' (wk1 A)⟩ with u⟨wk_up (Γ := Γ,,A') A' (wk1 A')⟩ in hinst.
  rewrite !wk1_eta in hinst; tea.
  eapply wk1_eta.
Qed.

Lemma instKripkeFamConv {Γ A A' B B' l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  : [ Γ,,A' ||-<l> B ≅ B'].
Proof.
  unshelve eapply instKripkeFam.
  2: intros; symmetry; eauto.
  1,2: tea.
  unshelve (intros; eapply hB; now eapply SirrLRSym); tea.
Qed.




Lemma instKripkeFamConvTm {Γ A A' B B' t u l} (wfΓ : [|-Γ])
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- t⟨wk_up A ρ⟩[a ..] ≅ u⟨wk_up A' ρ⟩[b ..] : _])
  : [ instKripkeFamConv wfΓ hB |  Γ ,, A' ||- t ≅ u : _].
Proof.
  eapply irrLR.
  unshelve eapply instKripkeFamTm.
  2,3: tea.
  2: intros; symmetry; eauto.
  1: unshelve (intros; eapply hB; now eapply SirrLRSym); tea.
  intros; unshelve eapply irrLR, eq; tea; now eapply SirrLRSym.
Qed.

Lemma instKripkeSubst {Γ A A' B B' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  (RA : [Γ ||-S<l> A ≅ A'])
  [t t']
  (ht : [_ ||-S<l> t ≅ t' : _ | RA])
  : [ Γ ||-<l> B[t..] ≅ B'[t'..]].
Proof.
  assert (wfΓ: [|-Γ]) by (escape; gtyping).
  specialize (hB Γ t t' wk_id wfΓ).
  rewrite 2wk_up_wk_id, 2wk_id_ren_on in hB.
  eapply hB.
  eapply SirrLREq, ht.
  now rewrite wk_id_ren_on.
Qed.

Lemma instKripkeSubst' {Γ A A' B B' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  (hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]])
  (RA : [Γ ||-<l> A ≅ A'])
  [t t']
  (ht : [_ ||-<l> t ≅ t' : _ | RA])
  : [ Γ ||-<l> B[t..] ≅ B'[t'..]].
Proof.
  eapply (dSplit_bind ht).
  intros ??? oRA oht.
  eapply WAdrefold.
  specialize (hB _ t⟨ρ⟩ t'⟨ρ⟩ ρ wfΔ).
  rewrite <- !subst_ren_wk_up in hB.
  now unshelve eapply hB, SirrLR, ht.
Qed.

Lemma instKripkeSubstTm {Γ A A' B B' u u' l}
  {hA : forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), [Δ ||-S<l> A⟨ρ⟩ ≅ A'⟨ρ⟩]}
  {hB : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [Δ ||-<l> B⟨wk_up A ρ⟩[a ..] ≅ B'⟨wk_up A' ρ⟩[b ..]]}
  (eq : forall Δ a b (ρ : Δ ≤ Γ) (wfΔ : [|-Δ])
    (hab : [hA Δ ρ wfΔ | Δ ||- a ≅ b : _]),
    [hB Δ a b ρ wfΔ hab | Δ ||- u⟨wk_up A ρ⟩[a ..] ≅ u'⟨wk_up A' ρ⟩[b ..] : _])
  (RA : [Γ ||-S<l> A ≅ A'])
  [t t' ]
  (ht : [_ ||-S<l> t ≅ t' : _ | RA])
  : [ _ ||-<l> u[t..] ≅ u'[t'..] : _ | instKripkeSubst hB RA ht].
Proof.
  assert (wfΓ: [|-Γ]) by (escape; gtyping).
  specialize (eq Γ t t' wk_id wfΓ).
  rewrite (@wk_up_wk_id Γ A u), (@wk_up_wk_id Γ A' u'),
    (wk_id_ren_on _ u), (wk_id_ren_on _ u') in eq.
  unshelve eapply irrLREq, eq; [|now rewrite wk_up_wk_id, wk_id_ren_on].
  eapply SirrLREq, ht.
  now rewrite wk_id_ren_on.
Qed.

End InstKripke.

(* 
Module WPolyRed.

Section WPolyRed.
  Context `{GenericTypingProperties}
    {Γ : context} {l : TypeLevel} {shp shp' pos pos' : term}.

  Record WPolyRed@{i j k l} : Type@{l} :=
    {
      shpRed : WLRAdequate@{i j k l} Γ l shp shp';
      posRed Δ wfΔ (ρ : Δ ≤ Γ) [a b] :
          [ Γ ||-< l > a ≅ b : shp⟨ρ⟩ | wkLRTy ρ wfΔ shpRed] ->
          WLRAdequate@{i j k l} Δ l pos[a .: ρ >> tRel] pos'[b .: ρ >> tRel] }.

  Definition PolyRed_return : [|-Γ] -> PolyRed Γ l shp shp' pos pos' -> WPolyRed.
  Proof.
    intros wfΓ P; unshelve econstructor.
    + eapply WAd_return.
      rewrite <- (wk_id_ren_on Γ shp), <- (wk_id_ren_on Γ shp').
      now eapply P.
    + intros * Rab.
      eapply (dSplit_bind Rab).
      intros Ξ wfΞ ρΞ owk oRab.
      eapply WAdrefold.
      rewrite <- 2 subst_ren_subst_mixed3.
      unshelve eapply P.(PolyRed.posRed); tea.
      unshelve eapply SirrLREq, Rab; tea.
      eapply wk_comp_ren_on.
  Qed.

End WPolyRed.

Arguments WPolyRed : clear implicits.
Arguments WPolyRed {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _.

End WPolyRed.

Export WPolyRed(WPolyRed,Build_WPolyRed). *)


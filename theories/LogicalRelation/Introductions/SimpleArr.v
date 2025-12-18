From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.

  Lemma shiftPolyRed {Γ}  {l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] -> PolyRed Γ l A A' B⟨↑⟩ B'⟨↑⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; now eapply SwkLR.
    - intros; rewrite 2!shift_subst_scons; now eapply WAd_return, SwkLR.
  Qed.

  Lemma ArrRedTy0 {Γ l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] -> [Γ ||-Π<l> arr A B ≅ arr A' B'].
  Proof.
    intros RA RB.
    eapply LRPiPoly0, shiftPolyRed; tea; escape; gtyping.
  Qed.

  Lemma ArrRedTy {Γ l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] -> [Γ ||-S<l> arr A B ≅ arr A' B'].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma polyRedArrExt {Γ l A A' B B' C C'} : PolyRed Γ l A A' B B' -> PolyRed Γ l A A' C C' -> PolyRed Γ l A A' (arr B C) (arr B' C').
  Proof.
    intros [RA RB] [RA' RC]; unshelve econstructor.
    1: eapply RA.
    intros ????? Rab.
    eapply SirrLR in Rab as Rab'.
    specialize (RB Δ a b ρ wfΔ Rab).
    specialize (RC Δ a b ρ wfΔ Rab').
    eapply (Split_bind RB).
    intros Ξ wfΞ ρΞ hRB.
    eapply WAdrefold.
    eapply (Split_wk_bind_return RC wfΞ ρΞ).
    intros Θ wfΘ ρΘ oRC.
    rewrite 2!subst_arr, 2!wk_comp_ren_on, <-2!wk_arr.
    eapply ArrRedTy.
    + now eapply RB, overtree_PSh.
    + now eapply RC.
  Qed.

  Lemma simple_appcongTerm {Γ t t' u u' F F' G G' l}
    {RF : [Γ ||-S<l> F ≅ F']}
    (RG : [Γ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-S<l> arr F G ≅ arr F' G'])
    (Rtt' : [Γ ||-S<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-S<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    unshelve (eapply irrLREq, appcongTerm; tea); tea;
    erewrite !shift_subst1; tea; reflexivity.
  Qed.

  Lemma simple_appcongTerm' {Γ t t' u u' F F' G G' l}
    {RF : [Γ ||-<l> F ≅ F']}
    (RG : [Γ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-<l> arr F G ≅ arr F' G'])
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    eapply (dSplit_bind Ruu').
    intros ??? oRF oRuu'.
    eapply (dSplit_wk_bind Rtt' wfΔ ρ).
    intros ??? oRΠ oRtt'.
    eapply Split_hom_PSh, (Wpackrefold wfΞ).
    1: intros Θ wfΘ ρΘ h oRG; rewrite wk_comp_assoc; eapply h.
    rewrite <- 2!wk_app.
    unshelve eapply simple_appcongTerm, Ruu', overtree_PSh, oRuu'; tea.
    1: rewrite 2!wk_arr; now eapply RΠ, oRΠ.
    1: now eapply overtree_PSh.
    unshelve eapply SirrLREq, Rtt'; tea.
    now bsimpl.
  Qed.

End SimpleArrow.

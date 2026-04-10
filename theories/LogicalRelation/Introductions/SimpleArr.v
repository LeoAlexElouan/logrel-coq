From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SimpleArrow.
  Context `{GenericTypingProperties}.

  Lemma shiftPolyRed {Γ}  {l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] ->
    PolyRed Γ l A A' B⟨@wk1 Γ A⟩ B'⟨@wk1 Γ A'⟩.
  Proof.
    intros; escape; unshelve econstructor.
    - intros; now eapply SwkLR.
    - intros. rewrite <- 2wk_up_wk1, 2shift_subst1.
      now eapply WAd_return, SwkLR.
  Qed.

  Lemma ArrRedTy0 {Γ l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] ->
    [Γ ||-Π<l> arr' Γ A B ≅ arr' Γ A' B'].
  Proof.
    intros RA RB.
    eapply LRPiPoly0, shiftPolyRed; tea; escape; gtyping.
  Qed.

  Lemma SArrRedTy {Γ l A A' B B'} : [Γ ||-S<l> A ≅ A'] -> [Γ ||-S<l> B ≅ B'] ->
    [Γ ||-S<l> arr' Γ A B ≅ arr' Γ A' B'].
  Proof. intros; eapply LRPi'; now eapply ArrRedTy0. Qed.

  Lemma ArrRedTy {Γ l A A' B B'} : [Γ ||-<l> A ≅ A'] -> [Γ ||-<l> B ≅ B'] ->
    [Γ ||-<l> arr' Γ A B ≅ arr' Γ A' B'].
  Proof. 
    intros RA RB.
    eapply (Split_bind RA).
    intros Δ wfΔ ρ oRA.
    eapply (Split_wk_bind_return RB wfΔ ρ).
    intros Ξ wfΞ ρΞ oRB.
    rewrite <- 2wk_arr'.
    eapply SArrRedTy.
    + now eapply RA, overtree_PSh.
    + now eapply RB.
  Qed.

  Lemma polyRedArrExt {Γ l A A' B B' C C'} : PolyRed Γ l A A' B B' ->
    PolyRed Γ l A A' C C' -> PolyRed Γ l A A' (arr' (Γ,,A) B C) (arr' (Γ,,A') B' C').
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
    rewrite <- 2wk_arr', <- 2!(WeakeningCompute.subst_arr' (Δ:=Δ)), 2!wk_comp_ren_on, <-2!wk_arr'.
    eapply SArrRedTy.
    + now eapply RB, overtree_PSh.
    + now eapply RC.
  Qed.

  Lemma Ssimple_appcongTerm {Γ t t' u u' F F' G G' l}
    {RF : [Γ ||-S<l> F ≅ F']}
    (RG : [Γ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-S<l> arr' Γ F G ≅ arr' Γ F' G'])
    (Rtt' : [Γ ||-S<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-S<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    unshelve (eapply irrLREq, SappcongTerm; tea); tea;
    erewrite !shift_subst1; tea; reflexivity.
  Qed.

  Lemma simple_appcongTerm {Γ t t' u u' F F' G G' l}
    {RF : [Γ ||-<l> F ≅ F']}
    (RG : [Γ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-<l> arr' Γ F G ≅ arr' Γ F' G'])
    (Rtt' : [Γ ||-<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-<l> u ≅ u' : F | RF ]) :
      [Γ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    eapply (dSplit_bind Ruu').
    intros ??? oRF oRuu'.
    eapply (dSplit_wk_bind Rtt' wfΔ ρ).
    intros ??? oRΠ oRtt'.
    eapply Split_hom_PSh, (Wpackrefold wfΞ).
    1:{ intros Θ wfΘ ρΘ h; rewrite wk_comp_assoc; eapply h. }
    rewrite <- 2!wk_app.
    unshelve eapply Ssimple_appcongTerm, Ruu', overtree_PSh, oRuu'; tea.
    1: rewrite 2!wk_arr'; now eapply RΠ, oRΠ.
    1: now eapply overtree_PSh.
    unshelve eapply SirrLREq, Rtt'; tea.
    now rewrite wk_arr'.
  Qed.

End SimpleArrow.

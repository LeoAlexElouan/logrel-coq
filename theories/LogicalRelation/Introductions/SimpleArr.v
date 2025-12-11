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
    eapply (Split_wk_bind_return RC ρΞ).
    intros Θ wfΘ ρΘ oRC.
    rewrite 2!subst_arr, 2!wk_comp_ren_on, <-2!wk_arr.
    eapply ArrRedTy.
    + now eapply RB, overtree_PSh.
    + now eapply RC.
  Qed.

  Lemma simple_appcongTerm {Γ} {wfΓ : [|-Γ]} {t t' u u' F F' G G' l}
    {RF : [Γ ||-S<l> F ≅ F']}
    (RG : [wfΓ ||-<l> G ≅ G'])
    (RΠ : [Γ ||-S<l> arr F G ≅ arr F' G'])
    (Rtt' : [Γ ||-S<l> t ≅ t' : _ | RΠ])
    (Ruu' : [Γ ||-S<l> u ≅ u' : F | RF ]) :
      [wfΓ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    unshelve (eapply irrLREq, appcongTerm; tea); tea;
    erewrite !shift_subst1; tea; reflexivity.
  Qed.

  Lemma simple_appcongTerm' {Γ} {wfΓ : [|-Γ]} {t t' u u' F F' G G' l}
    {RF : [wfΓ ||-<l> F ≅ F']}
    (RG : [wfΓ ||-<l> G ≅ G'])
    (RΠ : [wfΓ ||-<l> arr F G ≅ arr F' G'])
    (Rtt' : [wfΓ ||-<l> t ≅ t' : _ | RΠ])
    (Ruu' : [wfΓ ||-<l> u ≅ u' : F | RF ]) :
      [wfΓ ||-<l> tApp t u ≅ tApp t' u' : G | RG].
  Proof.
    eapply (dSplit_bind Ruu').
    intros ??? oRF oRuu'.
    eapply (dSplit_wk_bind Rtt' ρ).
    intros ??? oRΠ oRtt'.
    eapply (Split_assoc (A := fun Δ wfΔ ρ => forall ohA, [cover RG Δ wfΔ ρ ohA | Δ ||- _⟨ρ⟩ ≅ _⟨ρ⟩ : _⟨ρ⟩ ≅ _⟨ρ⟩])).
    eapply Wpackrefold.
    cbn -[Wpack wk_well_wk_compose].
    unshelve eapply simple_appcongTerm, Ruu', overtree_PSh, oRuu'; tea.
    1: rewrite 2!wk_arr; now eapply RΠ, oRΠ.
    1: now eapply overtree_PSh.
    unshelve eapply SirrLREq, Rtt'; tea.
    now bsimpl.
    Unshelve. tea.
  Qed.

End SimpleArrow.

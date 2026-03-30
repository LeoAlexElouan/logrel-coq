From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Lemma ScodSubst {Γ u u' F F' G G' l l'}
  (RΠ : [Γ ||-S<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-S<l'> F ≅ F']}
  (Ruu' : [Γ ||-S<l'> u ≅ u' : F | RF ]) :
  [Γ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  eapply instKripkeSubst, SirrLR, Ruu'.
  intros; eapply RΠ'.(PolyRed.posRed); eapply SirrLR, hab.
  Unshelve.
  2: eapply SinstKripke.
  1,3: eapply RΠ'.(PolyRed.shpRed).
  1:escape; gtyping.
  easy.
Qed.

Lemma codSubst {Γ u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]) :
  [Γ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  eapply (dSplit_bind Ruu').
  intros Δ wfΔ ρ oRF oRuu'.
  eapply WAdrefold, (Split_wk_bind RΠ wfΔ ρ).
  intros Ξ wfΞ ρΞ oRΠ.
  eapply WAdrefold.
  erewrite 2!wk_comp_ren_on.
  erewrite 2!(subst_ren_wk_up).
  unshelve eapply ScodSubst, Ruu'.
  3: now eapply RΠ. Unshelve.
  easy. 1,2: now eapply overtree_PSh.
  apply F. apply F'.
Qed.

Lemma SappcongTerm {Γ t t' u u' F F' G G' l l'}
  (RΠ : [Γ ||-S<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-S<l'> F ≅ F']}
  (Rtt' : [Γ ||-S<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-S<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..] ≅ G'[u'..]]) :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  assert [LRPi' RΠ' | _ ||- t ≅ t' : _ ] as [Rt Rt' ? app] by now eapply SirrLREq.
  eapply redSubstTmEq.
  + unshelve (eapply irrLREqCum, app; cbn; now rewrite wk_up_wk_id, wk_id_ren_on).
    3: eapply SirrLREqCum; tea; now rewrite wk_id_ren_on.
    escape; gtyping.
  + rewrite !wk_id_ren_on; eapply redtm_app; [now destruct (PiRedTmEq.red Rt)| now escape].
  + rewrite wk_id_ren_on; eapply redtm_app.
    2: eapply ty_conv; now escape.
    1: eapply redtm_conv; [now destruct (PiRedTmEq.red Rt')| now escape].
Qed.

Lemma appcongTerm {Γ t t' u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..] ≅ G'[u'..]]) :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  eapply (dSplit_bind Ruu').
  intros ??? oRF oRuu'.
  eapply Wpackrefold.
  eapply (dSplit_wk_bind Rtt' wfΔ ρ).
  intros Ξ wfΞ ρΞ oRΠ oRtt'.
  eapply Wpackrefold.
  rewrite wk_comp_ren_on, (wk_comp_ren_on (tApp t u)), <- 2wk_app.
  eapply irrLREq.
  1: symmetry; etransitivity; [ eapply wk_comp_ren_on |eapply (subst_ren_wk_up (A:=F))].
  unshelve eapply SappcongTerm.
  1: exact F⟨ρΞ ∘w ρ⟩.
  1: exact F'⟨ρΞ ∘w ρ⟩.
  1: exact G'⟨wk_up F' (ρΞ ∘w ρ)⟩.
  all: cycle 1.
  + rewrite 2 wk_prod.
    now eapply RΠ.
  + now eapply RF, overtree_PSh.
  + eapply SirrLREq.
    1: symmetry; eapply wk_prod.
    now unshelve now eapply Rtt'.
  + now eapply Ruu', overtree_PSh.
  Unshelve. all: tea.
  rewrite <- 2 subst_ren_wk_up.
  now eapply wkLRTy, RGu.
Qed.

End Application.




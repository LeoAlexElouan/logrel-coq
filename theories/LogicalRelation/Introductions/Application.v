From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Ltac fold_subst_term := fold subst_term in *.

Smpl Add fold_subst_term : refold.

Section Application.
Context `{GenericTypingProperties}.

Lemma ScodSubst {Γ} {wfΓ : [|-Γ]} {u u' F F' G G' l l'}
  (RΠ : [Γ ||-S<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-S<l'> F ≅ F']}
  (Ruu' : [Γ ||-S<l'> u ≅ u' : F | RF ]) :
  [wfΓ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  eapply instKripkeSubst, SirrLR, Ruu'.
  intros; eapply RΠ'.(PolyRed.posRed); eapply SirrLR, hab.
  Unshelve.
  3: eapply SinstKripke.
  2,4: eapply RΠ'.(PolyRed.shpRed).
  easy.
Qed.

Lemma codSubst {Γ} {wfΓ : [|-Γ]} {u u' F F' G G' l l'}
  (RΠ : [wfΓ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [wfΓ ||-<l'> F ≅ F']}
  (Ruu' : [wfΓ ||-<l'> u ≅ u' : F | RF ]) :
  [wfΓ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  eapply (dSplit_bind Ruu').
  intros Δ wfΔ ρ oRF oRuu'.
  eapply WAdrefold, (Split_wk_bind RΠ ρ).
  intros Ξ wfΞ ρΞ oRΠ.
  eapply WAdrefold.
  erewrite 2!wk_comp_ren_on.
  erewrite 2!(subst_ren_wk_up).
  unshelve eapply ScodSubst, Ruu'.
  3: now eapply RΠ. Unshelve.
  easy. 1,2: now eapply overtree_PSh.
  apply F. apply F'.
Qed.

Lemma appcongTerm {Γ} {wfΓ : [|-Γ]} {t t' u u' F F' G G' l l'}
  (RΠ : [Γ ||-S<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-S<l'> F ≅ F']}
  (Rtt' : [Γ ||-S<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-S<l'> u ≅ u' : F | RF ])
  (RGu : [wfΓ ||-<l'> G[u..] ≅ G'[u'..]]) :
    [wfΓ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  assert [LRPi' RΠ' | _ ||- t ≅ t' : _ ] as [Rt Rt' ? app] by now eapply SirrLREq.
  eapply redSubstTmEq.
  + unshelve (eapply irrLREqCum, app; cbn; now erewrite eq_subst_scons).
    2: rewrite wk_id_ren_on; eapply SirrLREqCum; tea; now rewrite wk_id_ren_on.
  + rewrite 2!wk_id_ren_on; eapply redtm_app; [now destruct (PiRedTmEq.red Rt)| now escape].
  + rewrite wk_id_ren_on; eapply redtm_app.
    2: eapply ty_conv; now escape.
    1: eapply redtm_conv; [now destruct (PiRedTmEq.red Rt')| now escape].
Qed.

End Application.



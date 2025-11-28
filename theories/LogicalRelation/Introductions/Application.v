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
  eapply instKripkeSubst, SirrLR, Ruu'. shelve.
  intros; eapply RΠ'.(PolyRed.posRed); eapply SirrLR, hab.
  Unshelve.
  3: eapply instKripke.
  2,4: eapply RΠ'.(PolyRed.shpRed).
  3: tea.
  all: escape; gtyping.
Qed.

Lemma codSubst {Γ u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ]) :
  [Γ ||-<l> G[u..] ≅ G'[u'..]].
Proof.
  eapply (dSplit_bind_over Ruu').
  intros Δ ρ oRF oRuu'.
  eapply WrePack, (Split_wk_bind_over RΠ ρ).
  intros Ξ ρΞ oRΠ.
  eapply WrePack.
  erewrite 2!wk_comp_ren_on.
  erewrite 2!(subst_ren_wk_up).
  eapply ScodSubst, Ruu', overtree_PSh, oRuu'.
  eapply RΠ.

Lemma appcongTerm {Γ t t' u u' F F' G G' l l'}
  (RΠ : [Γ ||-<l> tProd F G ≅ tProd F' G'])
  {RF : [Γ ||-<l'> F ≅ F']}
  (Rtt' : [Γ ||-<l> t ≅ t' : tProd F G | RΠ])
  (Ruu' : [Γ ||-<l'> u ≅ u' : F | RF ])
  (RGu : [Γ ||-<l'> G[u..] ≅ G'[u'..]]) :
    [Γ ||-<l'> tApp t u ≅ tApp t' u' : G[u..] | RGu].
Proof.
  set (RΠ' :=normRedΠ RΠ).
  assert [LRPi' RΠ' | _ ||- t ≅ t' : _ ] as [Rt Rt' ? app] by now eapply irrLREq.
  assert (wfΓ : [|-Γ]) by (escape ; gtyping).
  eapply redSubstTmEq.
(*   + unshelve (eapply irrLREqCum, app; cbn; now erewrite eq_subst_scons); [|tea|].
    2: rewrite wk_id_ren_on; eapply irrLREqCum; tea; now rewrite wk_id_ren_on.
  + rewrite 2!wk_id_ren_on; eapply redtm_app; [now destruct (PiRedTmEq.red Rt)| now escape].
  + rewrite wk_id_ren_on; eapply redtm_app.
    2: eapply ty_conv; now escape.
    1: eapply redtm_conv; [now destruct (PiRedTmEq.red Rt')| now escape]. *)
Admitted.

End Application.



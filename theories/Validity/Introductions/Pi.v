From Stdlib Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section PiValidity.

  Context `{GenericTypingProperties}.

  Lemma validΠdom {Γ Γ' F F' G G' l}
    {VΓ : [||-v Γ ≅ Γ']}
    (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]) :
    [Γ ||-v<l> F ≅ F' | VΓ].
  Proof.
    constructor; intros ? wfΔ ?? Vσ.
    pose proof (RΠ := validTyExt VΠ wfΔ Vσ).
    rewrite 2!subst_prod in RΠ.
    eapply Split_hom_PSh, RΠ.
    intros Ξ wfΞ ρΞ RΠ'.
    eapply (SinstKripke wfΞ (normRedΠ RΠ').(PolyRed.shpRed)).
  Qed.

  Lemma validΠcod {Γ Γ' F F' G G' l}
    {VΓ : [||-v Γ ≅ Γ']}
    (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ]) :
    [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ (validΠdom VΠ)].
  Proof.
    constructor; intros ? wfΔ ?? [Vσ hd].
    pose proof (RΠ := validTyExt VΠ wfΔ Vσ).
    rewrite 2!subst_prod in RΠ.
    eapply (Split_bind RΠ).
    intros Ξ wfΞ ρΞ oRΠ.
    eapply WAdrefold.
    eapply (dSplit_wk_bind hd wfΞ ρΞ).
    intros Θ wfΘ ρΘ oVΠ ohd.
    eapply WAdrefold.
    rewrite 2 wk_comp_ren_on.
    eapply overtree_PSh in oRΠ.
    set (RΠ' := cover RΠ _ wfΘ (ρΘ ∘w ρΞ) oRΠ). cbn -[ren1] in RΠ'.
    rewrite <- 2!wk_prod in RΠ'.
    set (hd' := cover hd _ wfΘ (ρΘ ∘w ρΞ) ohd oVΠ). cbn in hd'.
    rewrite <- 1!(eta_up_single_subst G), <- (eta_up_single_subst G').
    generalize (instKripkeSubst (normRedΠ RΠ').(PolyRed.posRed) _ hd').
    cbn -[wk1 ren_term]. now rewrite <- 2!subst_ren_wk_up, 2!eta_up_single_subst.
  Qed.

  Lemma substSΠ {Γ Γ' F F' G G' t u l}
    {VΓ : [||-v Γ ≅ Γ']}
    (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ])
    (Vt : [Γ ||-v<l> t ≅ u : F | VΓ | validΠdom VΠ]) :
    [_ ||-v<l> G[t..] ≅ G'[u..] | VΓ].
  Proof. eapply substS ; tea. eapply validΠcod. Qed.

  Definition PiValid {l Γ Γ' F F' G G'} (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-v< l > F ≅ F' | VΓ ])
    (VG : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF]) :
    [Γ ||-v< l > tProd F G ≅ tProd F' G' | VΓ].
  Proof.
    constructor; intros; rewrite 2!subst_prod.
    set (VF' := VF).
    destruct VF' as [RF'].
    specialize (RF' _ _ _ _ vσσ') as RF.
    eapply (Split_bind_return RF).
    intros Ξ wfΞ ρΞ oRF.
    rewrite <- 2!wk_prod.
    eapply LRPiPoly; tea.
    opector.
    + intros Θ ρΘ wfΘ. rewrite 2!wk_comp_ren_on.
      eapply overtree_PSh in oRF.
      now eapply RF.
    + intros Θ a b ρΘ wfΘ Rab.
      rewrite <- 2!wk_up_ren_subst, 2! eq_subst_2.
      unshelve (eapply validTyExt; tea); tea; unshelve eapply consWkSubst; tea.
      eapply irrLREq, (Wpack_return Rab).
      eapply wk_comp_ren_on.
  Qed.


  Lemma PiValidU {Γ Γ' F F' G G'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VF : [ Γ ||-v< one > F ≅ F' | VΓ ])
    (VΓF := validSnoc VΓ VF)
    (VG : [ Γ ,, F ||-v< one > G ≅ G' | VΓF])
    (VU : [ Γ ||-v< one > U | VΓ ])
    (VU' : [ Γ ,, F ||-v< one > U | VΓF ])
    (VFU : [ Γ ||-v< one > F ≅ F' : U | VΓ | VU ])
    (VGU : [ Γ ,, F ||-v< one > G ≅ G' : U | VΓF | VU' ]) :
    [ Γ ||-v< one > tProd F G ≅ tProd F' G' : U | VΓ | UValid VΓ ].
  Proof.
    constructor; intros ? wfΔ0 ?? Vσ. cbn -[Wpack].
    pose proof (univValid zero VFU) as VF0.
    pose proof (univValid zero VGU) as VG0.
    pose (v := validSnoc VΓ (urefl VF)).
    assert [_ ||-v<one> G ≅ G' : _ | _ | UValid v] by irrValid.
    pose proof (Vuσ := liftSubst' VF Vσ).
    pose proof (Vuσ' := liftSubst' (urefl VF) (urefl Vσ)).
    instValid Vuσ'.
    instValid Vuσ; instValid Vσ ; escape.
    eapply irrValidTyRfl in VG0 as VG0'.
    epose proof (PiValid VΓ VF0 VG0') as [RΠ].
    specialize (RΠ _ _ _ _ Vσ).
    eapply Split_hom_PSh, RΠ.
    intros Ξ wfΞ ρΞ RΠ' oLRU.
    unshelve (eapply SirrLREq; [easy|]).
    2:{ eapply (LRU_ (Universe.redUOneCtx wfΞ)). }
    unshelve econstructor.
    1,2: econstructor; [apply redtmwf_refl; cbn; eapply ty_prod; tea| constructor].
    5: cbn in *; refine (convtm_prod _ _ _).
    1,5: exact (ty_wk ρΞ wfΞ EscLRlVFU).
    1: exact (ty_wk (wk_up F[σ] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscLRVF)) EscLRlVGU).
    1: exact (ty_wk ρΞ wfΞ EscRRrVFU).
    1: exact (ty_wk (wk_up F'[σ'] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscRRVF)) EscRRrX).
    1: exact (convtm_wk ρΞ wfΞ EscRVFU).
    1: exact (convtm_wk (wk_up F[σ] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscLRVF)) EscRVGU).
    enough (h : [ Ξ ||-S< zero > (tProd F G)[σ]⟨ρΞ⟩ ≅ (tProd F' G')[σ']⟨ρΞ⟩]) by exact (cumLR h).
    eapply RΠ'.
  Qed.

End PiValidity.

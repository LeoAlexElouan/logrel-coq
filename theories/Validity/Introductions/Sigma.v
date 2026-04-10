From Stdlib Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Poly Sigma.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly ValidityTactics.


Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section SigmaCongRed.

Context `{GenericTypingProperties}.

Lemma validΣdom {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ]) :
  [Γ ||-v<l> F ≅ F' | VΓ].
Proof.
  constructor; intros ? wfΔ ?? Vσ; eapply redΣdom, (validTyExt VΣ wfΔ Vσ).
Qed.

Lemma validΣcod {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ]) :
  [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ (validΣdom VΣ)].
Proof.
  constructor; intros ? wfΔ ?? [Vσ hd].
  pose proof (RΣ := validTyExt VΣ wfΔ Vσ).
  rewrite <- 2!subst_sig in RΣ.
  pose proof (RG := redΣcodfst RΣ hd).
  rewrite 2to_subst_sound, 2subst_comp_on in RG.
  replace G[_] with G[σ] in RG by now rewrite eta_up_single_subst.
  now replace G'[_] with G'[σ'] in RG by now rewrite eta_up_single_subst.
Qed.

Lemma substSΣ {Γ Γ' F F' G G' t u l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VΣ : [Γ ||-v<l> tSig F G ≅ tSig F' G' | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u : F | VΓ | validΣdom VΣ]) :
  [_ ||-v<l> G[t..] ≅ G'[u..] | VΓ].
Proof. eapply substS ; tea; eapply validΣcod. Qed.

(* Lemma SigRed {Γ Γ' F G F' G' l}
  (VΓ : [||-v Γ ≅ Γ'])
  (VF : [ Γ ||-v< l > F ≅ F' | VΓ ])
  (VG : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF ])
  {Δ σ σ'} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ])
  : [ Δ ||-< l > (tSig F G)[σ] ≅ (tSig F' G')[σ'] ].
Proof.
  rewrite 2!subst_sig; eapply LRSig', substParamRedTy; tea; intros; gtyping.
Qed. *)

(* Lemma ValidWPolyRed {Γ Γ' F G F' G' l}
  (VΓ : [||-v Γ ≅ Γ'])
  (VF : [ Γ ||-v< l > F ≅ F' | VΓ ])
  (VG : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF ]) :
  WPolyRed Γ l F F' G G'.
Proof.
  unshelve econstructor.
  + now eapply redValidTy.
  + intros Δ wfΔ ρ a b Rab.
    change (ρ >> tRel) with tRel⟨ρ⟩.
    unshelve (eapply validTyExt; tea); tea; unshelve eapply consWkSubst, irrLREq, Rab; tea.
    1: now eapply escapeValid.
    2: now rewrite subst_rel.
    eapply idSubst.
Qed. *)

Lemma SigValid {Γ Γ' F G F' G' l}
  (VΓ : [||-v Γ ≅ Γ'])
  (VF : [ Γ ||-v< l > F ≅ F' | VΓ ])
  (VG : [ Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF ])
  : [Γ ||-v< l > tSig F G ≅ tSig F' G' | VΓ].
Proof.
  constructor; intros; rewrite <- 2!subst_sig.
  set (VF' := VF).
  destruct VF' as [RF'].
  specialize (RF' _ _ _ _ vσσ') as RF.
  eapply (Split_bind_return RF).
  intros Ξ wfΞ ρΞ oRF.
  rewrite <- 2!wk_sig.
  eapply SLRSigPoly; tea.
  opector.
  + intros Θ ρΘ wfΘ. rewrite 2!wk_comp_ren_on.
    eapply overtree_PSh in oRF.
    now eapply RF.
  + intros Θ a b ρΘ wfΘ Rab.
    rewrite 2(subst_ren_wk (A:=G)), 2(subst_ren_wk (A:=G')).
    replace G[_] with G[up_subst σ⟨ρΞ⟩⟨ρΘ⟩] by now rewrite 2eq_upwk.
    replace G'[_] with G'[up_subst σ'⟨ρΞ⟩⟨ρΘ⟩] by now rewrite 2eq_upwk.
    rewrite 2to_subst_sound, 2subst_comp_on.
    unshelve (eapply validTyExt; tea); tea.
    unshelve eapply consSubst, irrLREq, Wpack_return, Rab.
    - now unshelve eapply wkSubst, wkSubst.
    - now rewrite 2subst_ren_wk.
Qed.

End SigmaCongRed.


Section SigTmValidity.
  Context `{GenericTypingProperties}.

  Section Lemmas.
  Context {Γ Γ' F  F' G  G'} {VΓ : [||-v Γ ≅ Γ']}
    {VF : [ Γ ||-v< one > F ≅ F' | VΓ ]}
    (VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ])
    (VFeqU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGeqU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]).


  Lemma sigTmEq {Δ σ σ'} (tΔ : [ |-[ ta ] Δ])
    (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ ])
    : [Δ |-[ ta ] tSig F[σ] G[up_subst σ] ≅ tSig F'[σ'] G'[up_subst σ'] : U].
  Proof.
    pose proof (Vuσ := liftSubst' VF Vσσ').
    instValid Vσσ'; instValid Vuσ; escape.
    eapply convtm_sig; tea.
  Qed.


  Lemma SigURedTm {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ])
    : URedTm zero Δ (tSig F G)[σ].
  Proof.
    exists (tSig F G)[σ].
    2: constructor.
    pose proof (Vuσσ := liftSubst' VF Vσ); instValid Vσ ; instValid Vuσσ; escape;
      eapply redtmwf_refl; cbn; now eapply ty_sig.
  Defined.
  End Lemmas.

(*   Context {Γ Γ' F  F' G  G'} {VΓ : [||-v Γ ≅ Γ']}
    {VF : [ Γ ||-v< one > F ≅ F' | VΓ ]}
    {VU : [ Γ ,, F ||-v< one > U | validSnoc VΓ VF ]}
    (VFU : [ Γ ||-v< one > F ≅ F' : U | VΓ | UValid VΓ ])
    (VGU : [ Γ ,, F ||-v< one > G ≅ G' : U | validSnoc VΓ VF | VU ]). *)


  Lemma SigValidU {Γ Γ' F F' G G'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VF : [ Γ ||-v< one > F ≅ F' | VΓ ])
    (VΓF := validSnoc VΓ VF)
    (VU : [ Γ ||-v< one > U | VΓ ])
    (VU' : [ Γ ,, F ||-v< one > U | VΓF ])
    (VFU : [ Γ ||-v< one > F ≅ F' : U | VΓ | VU ])
    (VGU : [ Γ ,, F ||-v< one > G ≅ G' : U | VΓF | VU' ]) :
    [ Γ ||-v< one > tSig F G ≅ tSig F' G' : U | VΓ | UValid VΓ ].
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
    epose proof (SigValid VΓ VF0 VG0') as [RΠ].
    specialize (RΠ _ _ _ _ Vσ).
    eapply Split_hom_PSh, RΠ.
    intros Ξ wfΞ ρΞ RΠ' oLRU.
    unshelve (eapply SirrLREq; [easy|]).
    2:{ eapply (LRU_ (Universe.redUOneCtx wfΞ)). }
    unshelve econstructor.
    1,2: econstructor; [apply redtmwf_refl; cbn; eapply ty_sig; tea| constructor].
    5: cbn in *; refine (convtm_sig _ _ _).
    1,5: exact (ty_wk ρΞ wfΞ EscLRlVFU).
    1: exact (ty_wk (wk_up F[σ] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscLRVF)) EscLRlVGU).
    1: exact (ty_wk ρΞ wfΞ EscRRrVFU).
    1: exact (ty_wk (wk_up F'[σ'] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscRRVF)) EscRRrX).
    1: exact (convtm_wk ρΞ wfΞ EscRVFU).
    1: exact (convtm_wk (wk_up F[σ] ρΞ) (wfc_cons wfΞ (wft_wk ρΞ wfΞ EscLRVF)) EscRVGU).
    enough (h : [ Ξ ||-S< zero > (tSig F G)[σ]⟨ρΞ⟩ ≅ (tSig F' G')[σ']⟨ρΞ⟩]) by exact (cumLR h).
    eapply RΠ'.
  Qed.

End SigTmValidity.


Section ProjRed.
  Context `{GenericTypingProperties}.

  Context {l Γ Γ' F F' G G' } (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-v< l > F ≅ F' | VΓ ])
    (VG : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF])
    (VΣ := SigValid VΓ VF VG).

  Lemma fstValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ]):
    [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VF].
  Proof.
    constructor; intros; instValid Vσσ'.
    change (tFst p)[σ] with (tFst p[σ]).
    change (tFst p')[σ'] with (tFst p'[σ']).
    eapply fstRed, RVp.
  Qed.

  Lemma subst_fst {t σ} : tFst t[σ] = (tFst t)[σ].
  Proof. reflexivity. Qed.

  Lemma sndValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) :
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst].
  Proof.
    constructor; intros; instValid Vσσ'. rewrite <- 2subst_snd.
    change (tSig ?F ?G)[?σ] with (tSig F[σ] G[up_subst σ]) in RVp.
    unshelve eapply irrLREq, sndRed, RVp.
    now rewrite !subst_ren_subst_up in RVGfst.
    now rewrite subst_ren_subst_up.
  Qed.

End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

  Lemma up_subst_single' t a σ : t[up_term_term σ][(a[σ])..] = t[a..][σ].
  Proof. now bsimpl. Qed.

  Lemma pairFstValid {Γ Γ' A B a b l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tFst (tPair A B a b) ≅ a : _ | VΓ | VA].
  Proof.
    eapply redSubstValid; tea.
    constructor; intros. rewrite <-subst_fst, <- subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
    eapply redtm_fst_beta; tea.
    now rewrite <- subst_ren_subst_up.
  Qed.

  Lemma pairSndValid {Γ Γ' A B a b l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b : B[a..] | VΓ | VBa])
    (Vfstall := pairFstValid VΓ VA VB Va Vb)
    (VBfst := substS VB Vfstall) :
    [Γ ||-v<l> tSnd (tPair A B a b) ≅ b : _ | VΓ | VBfst].
  Proof.
    eapply redSubstValid; cycle 1.
    + irrValid.
    + constructor; intros.
      rewrite subst_ren_subst_up, <-subst_snd, <-subst_fst, <- subst_pair.
      instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
      eapply redtm_snd_beta; tea.
      now rewrite <- subst_ren_subst_up.
  Qed.


  Lemma pairCongValid {Γ Γ' A A' B B' a a' b b' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A ≅ A' | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B ≅ B' | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a ≅ a' : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b ≅ b' : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b ≅ tPair A' B' a' b' : _ | VΓ | VΣ].
  Proof.
    constructor; intros; rewrite <- 2!subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ').
    eapply irrLREq; [now rewrite <- subst_sig|].
    eapply pairCongRed; tea.
    now eapply irrLRConv; tea; rewrite <-subst_ren_subst_up; eapply lrefl.
    Unshelve.
    1: assumption.
    now rewrite <- 2!subst_ren_subst_up.
  Qed.

  Lemma pairValid {Γ Γ' A A' B B' a a' b b' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [ Γ ||-v<l> A ≅ A' | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B ≅ B' | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Va : [Γ ||-v<l> a ≅ a' : A | VΓ | VA])
    (VBa := substS VB Va)
    (Vb : [Γ ||-v<l> b ≅ b' : B[a..] | VΓ | VBa]) :
    [Γ ||-v<l> tPair A B a b : _ | VΓ | VΣ].
  Proof. now eapply lrefl, pairCongValid. Qed.

  Lemma sigEtaEqValid {Γ A B p p' l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ])
    (Vp' : [Γ ||-v<l> p' : _ | VΓ | VΣ])
    (Vfstpp' : [Γ ||-v<l> tFst p ≅ tFst p' : _ | VΓ | VA])
    (Vfst := fstValid VΓ VA VB Vp)
    (VBfst := substS VB Vfst)
    (Vsndpp' : [Γ ||-v<l> tSnd p ≅ tSnd p' : _| VΓ | VBfst]) :
    [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ].
  Proof.
    constructor; intros.
    pose proof (substS VB Vfstpp').
    instValid Vσσ'.
    rewrite 2subst_ren_subst_up in RX.
    eapply irrLREq; [now rewrite <- subst_sig|].
    eapply sigEtaRed.
    + now eapply lrefl, irrLR.
    + now eapply urefl, irrLR.
    + tea.
    + eapply irrLREq; tea.
      now rewrite subst_ren_subst_up.
    Unshelve.
    3: eapply RX.
    tea.
  Qed.



  Lemma sigEtaValid {Γ A B p l}
    (VΓ : [||-v Γ])
    (VA : [ Γ ||-v<l> A | VΓ ])
    (VB : [ Γ ,, A ||-v<l> B | validSnoc VΓ VA])
    (VΣ := SigValid VΓ VA VB)
    (Vp : [Γ ||-v<l> p : _ | VΓ | VΣ]) :
    [Γ ||-v<l> tPair A B (tFst p) (tSnd p) ≅ p : _ | VΓ | VΣ].
  Proof.
    pose (Vfst := fstValid _ _ _ Vp).
    pose (Vsnd := sndValid _ _ _ Vp).
    pose proof (pairFstValid _ _ _ Vfst Vsnd).
    pose proof (pairSndValid _ _ _ Vfst Vsnd).
    pose proof (pairValid _ _ _ Vfst Vsnd).
    unshelve eapply sigEtaEqValid; tea.
    cbn in * ; irrValid.
  Qed.

End PairRed.





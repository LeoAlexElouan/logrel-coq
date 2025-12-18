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
  rewrite 2!subst_sig in RΣ.
  rewrite <- 1!(eta_up_single_subst G), <- (eta_up_single_subst G').
  eapply redΣcodfst, hd.
  eapply RΣ.
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
  constructor; intros; rewrite 2!subst_sig.
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
    rewrite <- 2!wk_up_ren_subst, 2! eq_subst_2.
    unshelve (eapply validTyExt; tea); tea; unshelve eapply consWkSubst; tea.
    eapply irrLREq, (Wpack_return Rab).
    eapply wk_comp_ren_on.
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
    : [Δ |-[ ta ] tSig F[σ] G[up_term_term σ] ≅ tSig F'[σ'] G'[up_term_term σ'] : U].
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


  Lemma PiValidU {Γ Γ' F F' G G'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VF : [ Γ ||-v< one > F ≅ F' | VΓ ])
    (VΓF := validSnoc VΓ VF)
    (VG : [ Γ ,, F ||-v< one > G ≅ G' | VΓF])
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
    (unshelve now eapply fstRed; eapply irrLR); refold; now rewrite <-?subst_sig.
  Qed.

  Lemma subst_fst {t σ} : tFst t[σ] = (tFst t)[σ].
  Proof. reflexivity. Qed.

  Lemma sndValid {p p'} (Vp : [Γ ||-v<l> p ≅ p' : _ | VΓ | VΣ])
    (VGfst := substS VG (fstValid Vp)) :
    [Γ ||-v<l> tSnd p ≅ tSnd p' : _ | VΓ | VGfst].
  Proof.
    constructor; intros; cbn -[Wpack]; instValid Vσσ'.
    unshelve (eapply irrLREq; [|now eapply sndRed, irrLR]); refold.
    4: exact RVΣ.
    + refold; rewrite 2!subst_fst, <-2!singleSubstComm'; eapply VGfst, Vσσ'.
    + now rewrite subst_fst, singleSubstComm'.
  Qed.

End ProjRed.



Section PairRed.
  Context `{GenericTypingProperties}.

  Lemma subst_sig {A B σ} : (tSig A B)[σ] = (tSig A[σ] B[up_term_term σ]).
  Proof. reflexivity. Qed.

  Lemma subst_pair {A B a b σ} : (tPair A B a b)[σ] = (tPair A[σ] B[up_term_term σ] a[σ] b[σ]).
  Proof. reflexivity. Qed.

  Lemma subst_snd {p σ} : (tSnd p)[σ] = tSnd p[σ].
  Proof. reflexivity. Qed.

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
    constructor; intros; rewrite <-subst_fst, subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
    eapply redtm_fst_beta; tea.
    now rewrite up_subst_single'.
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
      rewrite <-up_subst_single', subst_snd, <-subst_fst, subst_pair.
      instValid Vσσ'; instValid (liftSubst' VA Vσσ'); escape.
      eapply redtm_snd_beta; tea.
      now rewrite up_subst_single'.
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
    constructor; intros; rewrite 2!subst_pair.
    instValid Vσσ'; instValid (liftSubst' VA Vσσ').
    eapply irrLREq; [now rewrite subst_sig|].
    eapply pairCongRed; tea.
    now eapply irrLRConv; tea; rewrite up_subst_single'; eapply lrefl.
    Unshelve.
    1: now rewrite <-2!subst_sig.
    now rewrite 2!up_subst_single'.
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
    eapply irrLREq; [now rewrite subst_sig|].
    eapply sigEtaRed.
    + now eapply lrefl, irrLR.
    + now eapply urefl, irrLR.
    + tea.
    + eapply irrLREq; tea.
      now rewrite subst_fst, up_subst_single'.
    Unshelve.
    1: now erewrite <-2!subst_sig.
    now rewrite 2!subst_fst, 2!up_subst_single'.
  Qed.
(* 
  Lemma FequivValid {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) : Γ =ε Γ'.
  Proof.
    induction Γ, Γ', VΓ using validity_rect; tea.
  Qed.

(*   Lemma FSnocValidTy {Γ} {new} A . *)

  Lemma validFSnoc {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b}:
    new = new' :> nat -> [||-v Γ,, new ↦ b ≅ Γ',, new' ↦ b].
  Proof.
    intros.
    induction Γ, Γ', VΓ using validity_rect.
    + eapply validEmpty, Fequiv_Fup; now symmetry.
    + change [||-v Γ,, new ↦ b,,A ≅ Γ',, new' ↦ b,,A'].
      eapply validSnoc.
      constructor.
      intros * h.
      eapply (wkValidTy (wk_Fstep (new : newnat Γ) b wk_id)) in VA.
      rewrite 2!wk_Fstep_ren_on,  2!wk_id_ren_on in VA.
      eapply VA, h.
      Unshelve.
      easy.
  Defined.

  Lemma irrSubstEq {Γ0 Γ0' Γ1 Γ1'} {VΓ0 : [||-v Γ0 ≅ Γ0']} {VΓ1 : [||-v Γ1 ≅ Γ1']} :
    Γ0 = Γ1 ->
    forall {Δ} (wfΔ : [|- Δ]) {σ σ'},
    [Δ ||-v σ ≅ σ' : _ | VΓ0 | wfΔ ] ->
    [Δ ||-v σ ≅ σ' : _ | VΓ1 | wfΔ ].
  Proof.
    intros <- *.
    eapply convSubst.
  Qed.

  Lemma validFSnocSubst_in {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b σ σ'} {Δ wfΔ}
    ( e: new = new' :> nat) :
    [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ] -> in_Fctx Δ new b -> [Δ ||-v σ  ≅ σ' : Γ,, new ↦ b | validFSnoc VΓ e | wfΔ].
  Proof.
    revert σ σ'.
    induction Γ, Γ', VΓ using validity_rect; intros σ σ' [] hin.
    + constructor.
      now eapply Fwk_new.
    + econstructor.
      now eapply SirrLR.
      Unshelve.
      now unshelve now eapply irrelevanceSubst, IHVΓ.
  Qed.

  Lemma FSnocSubst {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) :
  forall {σ σ' Δ new b} (wfΔ : [|- Δ]) (wfΔnew : [|- Δ,, new ↦ b]),
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ,,new ↦ b ||-v σ ≅ σ' : Γ | VΓ | wfΔnew ].
  Proof.
    intros ???????. revert σ σ'.
    induction Γ, Γ', VΓ using validity_rect; intros ?? [].
    + constructor.
      now eapply Fwk_Fstep.
    + unshelve econstructor.
      now eapply IHVΓ.
      eapply (SirrLREq (A:= A[↑ >> σ]⟨wk_Fstep new b wk_id⟩)).
      etransitivity; [eapply wk_Fstep_ren_on | eapply wk_id_ren_on].
      rewrite <- (wk_id_ren_on Δ (σ var_zero)), <- (wk_id_ren_on Δ (σ' var_zero)),
        <- 2(wk_Fstep_ren_on new b).
      eapply SwkLR, eqHead.
      Unshelve.
      now eapply wfc_consF.
  Qed.

  Lemma validFSnocSubst_notin {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) {new : newnat Γ} {new' : newnat Γ'} {b σ σ'} {Δ wfΔ}
    ( e: new = new' :> nat) (Vσσ' : [Δ ||-v σ ≅ σ' : _ | VΓ | wfΔ]) (notinΔ : not_in_Fctx Δ new) :
      let newΔ := Build_newnat Δ new notinΔ in [Δ,,newΔ ↦ b ||-v σ  ≅ σ' : Γ,, new ↦ b | validFSnoc VΓ e | wfc_consF wfΔ].
  Proof.
    intros ?.
    eapply validFSnocSubst_in.
    now eapply FSnocSubst.
    cbn.
    eapply in_hereF.
  Qed.

  Lemma validTy_shf {Γ} {wfΓ : [|-Γ]} {VΓ : [||-v Γ]} {l A B} :
    shf wfΓ (fun Δ wfΔ ρ => forall (VΔ : [||-v Δ]), [Δ ||-v< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ]).
  Proof.
    intros ???? ht hf ?.
(*     set (new' := Build_newnat Δ' new (wk_new_notin new (lFwk (FequivValid VΔ)))). *)
    specialize (ht (validFSnoc VΔ eq_refl)).
    specialize (hf (validFSnoc VΔ eq_refl)).
    rewrite 2 !wk_Fstep_ren_on in ht,hf.
    constructor.
    intros Ξ wfΞ ???.
    destruct (decide_in Ξ new) as [ [] hin | hnotin].
    - eapply ht.
      eapply validFSnocSubst_in; tea.
    - eapply hf.
      eapply validFSnocSubst_in; tea.
    - eapply WAd_split.
      + eapply ht.
        now unshelve eapply validFSnocSubst_notin, vσσ'.
      + eapply hf.
        now unshelve eapply validFSnocSubst_notin, vσσ'.
  Qed.

  Lemma Split_bind_validTy {Γ} {wfΓ : [|-Γ]} {VΓ : [||-v Γ]} {l A B C } (hC : Split (wfΓ:=wfΓ) C) :
    (forall Δ (VΔ : [||-v Δ]) (ρ : Δ ≤ Γ), overtree hC Δ -> [Δ ||-v< l > A⟨ρ⟩ ≅ B⟨ρ⟩ | VΔ]) ->
    [Γ ||-v< l > A ≅ B | VΓ].
  Proof.
    intros hAB.
    rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ B).
    unshelve eapply (Split_bind_alg validTy_shf hC), wfΓ; tea.
    intros ??? ohC ?.
    now eapply hAB.
  Qed.
 *)



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





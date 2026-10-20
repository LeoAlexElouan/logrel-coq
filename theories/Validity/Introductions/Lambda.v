From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties Introductions.Lambda.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi Application Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

(* Lemma isLRFun_isWfFun `{GenericTypingProperties}
  {l Γ F F' G G' t} (RΠFG : [Γ ||-S< l > tProd F G ≅ tProd F' G'])
  (Rt : isLRFun (normRedΠ RΠFG) t)
  : isWfFun Γ F G t.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rt as [??? wtA convtyA eqt| | |].
  + epose proof (instKripkeFamTm wfΓ eqt).
    escape; now constructor.
  + now constructor.
  + now constructor.
  + now constructor.
Qed.
 *)

Section LambdaValid.
Context `{GenericTypingProperties}.
(* 
  Lemma LamLRFun' Γ l (A B : term) (ΠA : PiRedTy Γ l A B) : forall A' t : term,
    [Γ |- A'] -> [Γ |- PiRedTy.domL ΠA ≅ A'] ->
    (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |- Δ])
      (ha : [Δ ||-S< l > a ≅ b
        : _ | PolyRed.shpRed ΠA ρ wfΔ ]),
      [Δ ||-< l > t⟨wk_up (ParamRedTy.domL ΠA) ρ⟩[a ..] ≅ t⟨wk_up (ParamRedTy.domR ΠA) ρ⟩[b ..] :
        _ | PolyRed.posRed ΠA ρ wfΔ ha]) ->
    isLRFun ΠA (tLambda A' t).
  Proof.
    intros ?? HA' HΠA Rtt'.
    constructor; tea.
  Qed.

  Lemma irrFuneqs {l l1 l2 Γ A1 A2 B1 B2} (ΠA1: [Γ ||-Π< l1 > A1 ≅ B1]) (ΠA2: [Γ ||-Π< l2 > A2 ≅ B2])
    (RA : [Γ ||-S<l> A1 ≅ A2]) : ∑ R : [Γ ||-Π< l > A1 ≅ A2],
      [× RA = LRPi' R, ParamRedTy.domL R = ParamRedTy.domL ΠA1, ParamRedTy.domR R = ParamRedTy.domL ΠA2,
        ParamRedTy.codL R = ParamRedTy.codL ΠA1 & ParamRedTy.codR R = ParamRedTy.codL ΠA2].
  Proof.
    pose proof (invLREqL_whred (LRPi' ΠA1) RA) as (R&[? e1 e2]); cbn in e1,e2;
    pose proof (whredty_det (whredtyR R) (whredtyL ΠA2)) as [= e3 e4]; cbn.
    exists R.
    now split.
  Defined.

  Lemma irrisLRFun {l l1 l2 Γ A1 A2 B1 B2} {t} (ΠA1: [Γ ||-Π< l1 > A1 ≅ B1]) (ΠA2: [Γ ||-Π< l2 > A2 ≅ B2]) :
    [Γ ||-S<l> A1 ≅ A2] -> isLRFun ΠA1 t -> isLRFun ΠA2 t.
  Proof.
    intros RA isfun.
    pose proof (irrFuneqs ΠA1 ΠA2 RA) as (R&[-> edom1 edom2 ecod1 ecod2]).
    destruct isfun as [????? app| | | ].
    2-4 :constructor; first [ eapply convneu_conv; tea | etransitivity; tea; symmetry]; cbn;
      rewrite <- edom1, <- edom2, <- ecod1, <- ecod2;
      eapply R.
    apply LamLRFun'; tea.
    1: etransitivity ; tea; cbn; symmetry;
      rewrite <- edom1, <- edom2;
      eapply R.
    intros; eapply irrLRCum; [|eapply app].
    rewrite <- ecod1, <- ecod2.
    eapply R.(PolyRed.posRed), lrefl, SirrLRCum; tea.
    rewrite <- edom2; symmetry; now eapply R.(PolyRed.shpRed).
    Unshelve. all: tea.
    now eapply SirrLRCum; tea; symmetry; rewrite <- edom1, <- edom2; eapply R.(PolyRed.shpRed).
  Qed.

  Lemma isLRFun_isWfFun'
    {l Γ F F' G G' t} (RΠFG : [Γ ||-Π< l > tProd F G ≅ tProd F' G'])
    (Rt : isLRFun RΠFG t)
    : isWfFun Γ F G t.
  Proof.
    unshelve eapply isLRFun_isWfFun.
    4: now eapply LRPi'.
    eapply irrisLRFun, Rt.
    now eapply lrefl, LRPi'.
  Qed.

  Lemma irrPiRedTm {l l1 l2 Γ A1 A2 B1 B2} {t} (ΠA1: [Γ ||-Π< l1 > A1 ≅ B1]) (ΠA2: [Γ ||-Π< l2 > A2 ≅ B2]) :
    [Γ ||-S<l> A1 ≅ A2] -> PiRedTm ΠA1 t -> PiRedTm ΠA2 t.
  Proof.
    intros RA Rt.
    exists Rt.(PiRedTmEq.nf).
    1:pose proof (irrFuneqs ΠA1 ΠA2 RA) as (R&[e edom1 edom2 ecod1 ecod2]);
      eapply redtmwf_conv; [eapply Rt|]; cbn;
      rewrite <- edom1, <- edom2, <- ecod1, <- ecod2;
      eapply R.
    now eapply irrisLRFun, Rt.
  Defined.

(* Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed. *)
Lemma lamPiRedTm
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-S<l> tProd F[σ] G[up_subst σ] ≅ tProd F'[σ'] G'[up_subst σ']])
  : PiRedTm (normRedΠ R0) (tLambda F t)[σ].
Proof.
  set (R := normRedΠ R0). (* : [Δ ||-Π< l > (tProd F G)[σ] ≅ (tProd F' G')[σ']]). *)
  exists (tLambda F[σ] t[up_subst σ]);
  instValid (liftSubst' VF  Vσσ'); instValid Vσσ'; escape.
  1: now eapply redtmwf_refl, ty_lam.
  apply LamLRFun'; tea; [now eapply lrefl|].
  change (ParamRedTy.domL R) with F[σ].
  change (ParamRedTy.domR R) with F'[σ'].
  change (ParamRedTy.codL R) with G[up_subst σ].
  change (ParamRedTy.codR R) with G'[up_subst σ'].
  intros Ξ ?? ρΞ wfΞ ha.
  rewrite 2(subst_ren_wk (A:=t)),
    2to_subst_sound with (t:=t[_]),
    2subst_comp_on.
  unshelve eapply irrLREq, validTmExt, lrefl, Vtt'; tea.
  2: now rewrite <- subst_comp_on, <- to_subst_sound, <- subst_ren_wk.
  unshelve eapply irrelevanceSubstEqExt, consSubst.
  6,7: rewrite eq_upwk; reflexivity.
  + eapply wkSubst, lrefl, Vσσ'.
  + eapply irrLREq, Wpack_return, ha.
    now rewrite <- subst_ren_wk.
Defined.

Lemma lamPiRedTm'
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  (VΠFG := PiValid VΓ VF VG)
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-S<l> tProd F[σ] G[up_subst σ] ≅ tProd F'[σ'] G'[up_subst σ']])
  : PiRedTm (normRedΠ R0) (tLambda F' t')[σ'].
Proof.
  set (R := normRedΠ R0).
  eapply irrPiRedTm; [|eapply lamPiRedTm].
  + symmetry; eapply LRPi', R.
  + now eapply symValidTm.
  + now eapply symSubst.
  Unshelve. 1-3: irrValid.
  1: now symmetry.
  tea.
Defined.

(* Lemma isLRFun_wk
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  (VΠFG := PiValid VΓ VF VG)
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-S<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0) :
  isLRFun R (tLambda F t)[σ].
Proof.
  instValid (liftSubst' VF  Vσσ'); instValid Vσσ'; escape.
  apply LamLRFun'; tea; [now eapply lrefl|].
  intros Ξ ?? ρΞ wfΞ ha; rewrite 2!consWkEq'.
  pose (Vaσ := consWkSubstEq VF (lrefl Vσσ') ρΞ wfΞ (Wpack_return ha)).
  eapply irrLREq.
  2: now unshelve eapply (validTmExt (lrefl Vtt')).
  cbn; now rewrite consWkEq'.
Qed.
 *)
(* 
Lemma lamPiRedTmEq
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-S<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0)
  : PiRedTmEq R (tLambda F t)[σ] (tLambda F' t')[σ'].
Proof.
  refold.
  change (tLambda F t)[σ] with (tLambda F[σ] t[up_term_term σ]).
  change (tLambda F' t')[σ'] with (tLambda F'[σ'] t'[up_term_term σ']).
  unshelve refine (Build_PiRedTmEq _ _ _ _ _ _ _ _ _ _ _ _ R (tLambda F[σ] t[up_term_term σ]) (tLambda F'[σ'] t'[up_term_term σ']) _ _ _ _).
  now eapply lamPiRedTm.
  now eapply lamPiRedTm'.
  pose proof (Vuσ := liftSubst' VF Vσσ').
    pose proof (Vuσ' := liftSubstSym' VF Vσσ').
    pose proof (symValidTm' Vtt'); pose proof (symValidTy' VG).
  instValid (liftSubst' VF  Vσσ'); instValid Vσσ'; escape.
  cbn.
  eapply lambda_cong; tea.
  1: now eapply redtmwf_refl, ty_lam.
  apply LamLRFun'; tea; [now eapply lrefl|].
  intros Ξ ?? ρΞ wfΞ ha; rewrite 2!consWkEq'.
  pose (Vaσ := consWkSubstEq VF (lrefl Vσσ') ρΞ wfΞ (Wpack_return ha)).
  eapply irrLREq.
  2: now unshelve eapply (validTmExt (lrefl Vtt')).
  cbn; now rewrite consWkEq'.
Defined. *)
(* 
Definition Build_PiRedTmL Γ l A B (ΠA : PiRedTy Γ l A B) (t : term)
  (shp := PiRedTy.domL ΠA) (shp' := PiRedTy.domR ΠA)
  (pos := PiRedTy.codL ΠA) (pos' := PiRedTy.codR ΠA) :
  [Γ,,shp |- t : pos] ->
  isLRFun ΠA (tLambda shp t) -> PiRedTm ΠA (tLambda shp t).
Proof.
  intros ht hLRFun.
  exists (tLambda shp t).
  1: eapply redtmwf_refl, ty_lam; tea.
  1: eapply ΠA.
  eapply hLRFun.
Defined. *)


(* Definition Build_PiRedTmEq' Γ l A B (ΠA : PiRedTy Γ l A B) (t u : term)
  (shp := PiRedTy.domL ΠA) (shp' := PiRedTy.domR ΠA)
  (pos := PiRedTy.codL ΠA) (pos' := PiRedTy.codR ΠA) :
  isLRFun ΠA (tLambda shp t) ->
  isLRFun ΠA (tLambda shp u) ->
  [Γ,,shp |- t : pos] ->
  [Γ,,shp |- u : pos] ->
  [Γ,,shp |- t ≅ u : pos] ->
  (forall Δ ρ wfΔ a b
    (hab : [Δ ||-S< l > a ≅ b : shp⟨ρ⟩ | PolyRed.shpRed ΠA ρ wfΔ ]), 
    [Δ ||-< l > tApp (tLambda shp t)⟨ρ⟩ a ≅ tApp (tLambda shp' u)⟨ρ⟩ b : pos[a .: ρ >> tRel]
      | PolyRed.posRed ΠA ρ wfΔ hab]) ->
  [Γ ||-S< l > tLambda shp t ≅ tLambda shp' u : A | LRPi' ΠA]. *)



Lemma eqApp' {Γ l A B} {ΠA : [Γ ||-Π< l > A ≅ B]} {t u}
  (Rtu : [Γ ||-Π t ≅ u : _ | ΠA]) 
  (nfL := PiRedTmEq.nf (PiRedTmEq.redL Rtu)) (nfR := PiRedTmEq.nf (PiRedTmEq.redR Rtu)):
  forall {Δ} wfΔ ρ {a b} (hab : [Δ ||-S< l > a ≅ b : _ | PolyRed.shpRed ΠA ρ wfΔ]),
  [Δ ||-< l > (tApp nfL⟨ρ⟩ a) ≅ (tApp nfR⟨ρ⟩ b) :_ | PolyRed.posRed ΠA ρ wfΔ hab].
Proof.
  intros.
  eapply (PiRedTmEq.eqApp Rtu ρ wfΔ hab).
Qed. *)

(* Lemma consWkEq {Δ Ξ F} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed. *)

(* Lemma eq_subst_3 t a ρ σ : t[up_term_term σ][a .: ρ >> tRel] = t[up_term_term σ⟨ρ⟩][a..].
Proof.
  bsimpl ; now substify.
Qed. *)

(* Lemma eq_subst_4 t a σ : t[up_term_term σ][a..] = t[a .: σ].
Proof.
  bsimpl ; now substify.
Qed. *)

(* Lemma eq_substren {Γ Δ} t σ (ρ : Γ ≤ Δ) : t[σ]⟨ρ⟩ = t[σ⟨ρ⟩].
Proof. now asimpl. Qed. *)
Generalizable All Variables.
Lemma validLRExt {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  `(Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ ≅ Γ' | wfΔ]):
  LRExt (validTyExt VF wfΔ Vσσ') G[up_subst σ] G'[up_subst σ'].
Proof.
  intros Ξ wfΞ ρΞ ???.
  replace _[a..] with G[to_subst a.. ∘s up_subst (σ⟨ρΞ⟩)].
  replace _[b..] with G'[to_subst b.. ∘s up_subst (σ'⟨ρΞ⟩)].
  2-3: now rewrite ! to_subst_sound, ! subst_ren_wk, ! subst_comp_on, eq_upwk.
  unshelve eapply VG, consWkSubst, Rab; tea.
Qed.

Lemma validLRExtTm {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  `(Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  `(Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ ≅ Γ' | wfΔ]) :
  LRExtTm _ (validLRExt _ VG Vσσ') t[up_subst σ] t'[up_subst σ'].
Proof.
  intros Ξ wfΞ ρΞ ???.
  eapply irrLREq; cycle 1.
  replace _[a..] with t[to_subst a.. ∘s up_subst (σ⟨ρΞ⟩)].
  replace _[b..] with t'[to_subst b.. ∘s up_subst (σ'⟨ρΞ⟩)].
  2-3: now rewrite ! to_subst_sound, ! subst_ren_wk, ! subst_comp_on, eq_upwk.
  unshelve eapply Vtt'; tea.
  now eapply consWkSubst.
  now rewrite ! to_subst_sound, ! subst_ren_wk, ! subst_comp_on, eq_upwk.
Qed.


Context {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  (VΠFG := PiValid VΓ VF VG).

Lemma lamCongValid {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG]) :
  [Γ ||-v<l> tLambda F t ≅ tLambda F' t' : tProd F G | VΓ | VΠFG ].
Proof.
  constructor; intros.
  rewrite <-! subst_lam.
  unshelve eapply irrLREq, lamCongRed.
  + exact G[up_subst σ].
  + exact G'[up_subst σ'].
  + now eapply VF.
  + cbn zeta.
    now eapply validLRExt.
  + now rewrite subst_prod.
  + cbn zeta.
    now eapply validLRExtTm.
Qed.



Lemma lamValid {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG]) :
  [Γ ||-v<l> tLambda F t : tProd F G | VΓ | VΠFG ].
Proof.
  now eapply lrefl, lamCongValid.
Qed.

(* 
Lemma singleSubst_subst_eq t a σ : t[a..][σ] = t[up_term_term σ][a[σ]..].
Proof. now bsimpl. Qed.

Lemma singleSubst_subst_eq' t a σ : t[a..][σ] = t[a[σ] .: σ].
Proof. now bsimpl. Qed. *)

Lemma betaValid {t t' a a'} (Vt : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  (Va : [Γ ||-v<l> a ≅ a' : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va].
Proof.
  eapply redSubstValid.
  2: now eapply lrefl, substSTm.
  constructor; intros.
  rewrite <- subst_app, <- subst_lam,
    2subst_ren_subst_up.
(*   rewrite 2!singleSubst_subst_eq. *)
  instValid (lrefl Vσσ').
  instValid (liftSubst' VF (lrefl Vσσ')).
  escape; now eapply redtm_beta.
Qed.

Lemma etaExpandValid {f} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]) :
  [Γ ,, F ||-v<l> eta_expand' Γ F f : G | VΓF | VG].
Proof.
  unshelve epose (VF' := wkValidTy ρ _ _ VF); [|tea|].
  unshelve epose (wkValidTy ρ _ _ VΠFG); [|tea|].
  unshelve epose (wkValidTm ρ _ _ _ Vf); [|tea|].
  eapply irrValidTmRfl; cycle 1.
  + unshelve (eapply appcongValid, irrValidTmRfl; tea; symmetry; eapply wk_prod).
    4: unshelve (eapply irrValidTmRfl, var0Valid; reflexivity); tea.
    3: eapply wkValidTy with (1:= VΠFG).
  + eapply wk1_eta.
  Unshelve. tea.
Qed.

Lemma etaeqValid {f g}
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ])
  (Vfg : [Γ ,, F ||-v<l> (eta_expand' Γ F f) ≅ (eta_expand' Γ F g) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros ???? Vσ.
  unshelve eapply irrLREq, etaeqRed.
  1-4 : shelve.
  + eapply VF, Vσ.
  + eapply validLRExt, VG.
  + now rewrite <- subst_prod.
  + replace (tApp f[_]⟨_⟩ _) with (eta_expand' Γ F f)[up_subst σ].
    replace (tApp g[_]⟨_⟩ _) with (eta_expand' Γ F g)[up_subst σ'].
    2-3: now erewrite <- subst_app, <- subst_up_wk1.
    now unshelve now eapply irrLRExtTm, validLRExtTm.
  + unshelve eapply irrLR, Vf; tea.
    now eapply lrefl.
  + instValid Vσ.
    eapply irrLRConv; tea.
    rewrite subst_prod.
    eapply validTyExt.
    - now eapply lrefl.
    - now symmetry.
Qed.

End LambdaValid.


Section EtaValid.
Context `{GenericTypingProperties}.

Context {Γ F G l}
  {VΓ : [||-v Γ]}
  (VF : [Γ ||-v<l> F | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G | VΓF])
  (VΠFG := PiValid VΓ VF VG).


Lemma subst_rel0 t : t⟨↑⟩[(tRel 0)..] = t.
Proof. now bsimpl. Qed.

Lemma etaValid {f} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]) :
  [Γ ||-v<l> (tLambda F (eta_expand' Γ F f)) ≅ f : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros.
  erewrite <- subst_lam, <- subst_app, <- subst_up_wk1.
  etransitivity.
  eapply irrLREq, etaRed.
  + now rewrite <- subst_prod.
  + eapply lrefl.
    replace (tApp _ _) with (eta_expand' Γ F f)[up_subst σ]
    by now erewrite <- subst_app, subst_up_wk1.
    unshelve eapply validLRExtTm, etaExpandValid, Vf; tea.
    now eapply lrefl.
  + instValid Vσσ'.
    now eapply irrLR.
  + instValid Vσσ'.
    now eapply irrLR.
Qed.


End EtaValid.

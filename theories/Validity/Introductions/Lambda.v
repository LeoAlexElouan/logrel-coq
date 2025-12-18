From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi Application Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Lemma isLRFun_isWfFun `{GenericTypingProperties}
  {l Γ F F' G G' t} (RΠFG : [Γ ||-S< l > tProd F G ≅ tProd F' G'])
  (Rt : isLRFun (normRedΠ RΠFG) t)
  : isWfFun Γ F G t.
Proof.
  assert (wfΓ: [|- Γ]) by (escape ; gen_typing).
  destruct Rt as [?? wtA convtyA eqt|]; cbn in *.
  2: now constructor.
  epose proof (instKripkeFamTm wfΓ eqt).
  escape; now constructor.
Qed.


Section LambdaValid.
Context `{GenericTypingProperties}.

  Lemma LamLRFun' Γ l (A B : term) (ΠA : PiRedTy Γ l A B) : forall A' t : term,
    [Γ |- A'] -> [Γ |- PiRedTy.domL ΠA ≅ A'] ->
    (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (wfΔ : [ |- Δ])
      (ha : [Δ ||-S< l > a ≅ b
        : (ParamRedTy.domL ΠA)⟨ρ⟩ | PolyRed.shpRed ΠA ρ wfΔ ]),
      [Δ ||-< l > t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] :
        (PiRedTyPack.codL ΠA)[a .: ρ >> tRel] | PolyRed.posRed ΠA ρ wfΔ ha]) ->
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
    destruct isfun as [???? app|].
    2: constructor; eapply convneu_conv; [eapply c |]; cbn;
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

Lemma consWkEq' {Δ Ξ} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ][a .: ρ >> tRel] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.


Lemma lamPiRedTm
  {Γ Γ' F F' G G' l}
  {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VΓF := validSnoc VΓ VF)
  {VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF]}
  {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  {Δ} {wfΔ : [|-Δ]} {σ σ'} (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ])
  (R0 : [Δ ||-S<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0)
  : PiRedTm R (tLambda F t)[σ].
Proof.
  exists (tLambda F[σ] t[up_term_term σ]);
  instValid (liftSubst' VF  Vσσ'); instValid Vσσ'; escape.
  1: now eapply redtmwf_refl, ty_lam.
  apply LamLRFun'; tea; [now eapply lrefl|].
  intros Ξ ?? ρΞ wfΞ ha; rewrite 2!consWkEq'.
  pose (Vaσ := consWkSubstEq VF (lrefl Vσσ') ρΞ wfΞ (Wpack_return ha)).
  eapply irrLREq.
  2: now unshelve eapply (validTmExt (lrefl Vtt')).
  cbn; now rewrite consWkEq'.
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
  (R0 : [Δ ||-S<l> (tProd F G)[σ] ≅ (tProd F' G')[σ']])
  (R := normRedΠ R0)
  : PiRedTm R (tLambda F' t')[σ'].
Proof.
  eapply irrPiRedTm; [|eapply lamPiRedTm]; refold.
  + symmetry; now eapply LRPi'. (*  rewrite <-2!subst_prod. now eapply validTyExt. *)
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

Definition Build_PiRedTmEq' {Γ l A B} {ΠA : PiRedTy Γ l A B} {t u : term}
  (shp := PiRedTy.domL ΠA) (shp' := PiRedTy.domR ΠA)
  (pos := PiRedTy.codL ΠA) (pos' := PiRedTy.codR ΠA)
  (redL : PiRedTm ΠA t) (redR : PiRedTm ΠA u)
  (nfL := PiRedTmEq.nf redL) (nfR := PiRedTmEq.nf redR) :
  [Γ |- nfL ≅ nfR : tProd shp pos] ->
  (forall Δ ρ wfΔ a b
    (hab : [Δ ||-S< l > a ≅ b : shp⟨ρ⟩ | PolyRed.shpRed ΠA ρ wfΔ ]), 
    [Δ ||-< l > tApp nfL⟨ρ⟩ a ≅ tApp nfR⟨ρ⟩ b : pos[a .: ρ >> tRel]
      | PolyRed.posRed ΠA ρ wfΔ hab]) ->
  [Γ ||-Π t ≅ u : A | ΠA].
Proof.
  intros eq eqApp.
  econstructor.
  1: eapply eq.
  intros Δ a b ρ wfΔ hab.
  eapply eqApp.
Qed.


Lemma eqApp' {Γ l A B} {ΠA : [Γ ||-Π< l > A ≅ B]} {t u}
  (Rtu : [Γ ||-Π t ≅ u : _ | ΠA]) 
  (nfL := PiRedTmEq.nf (PiRedTmEq.redL Rtu)) (nfR := PiRedTmEq.nf (PiRedTmEq.redR Rtu)):
  forall {Δ} wfΔ ρ {a b} (hab : [Δ ||-S< l > a ≅ b : _ | PolyRed.shpRed ΠA ρ wfΔ]),
  [Δ ||-< l > (tApp nfL⟨ρ⟩ a) ≅ (tApp nfR⟨ρ⟩ b) :_ | PolyRed.posRed ΠA ρ wfΔ hab].
Proof.
  intros.
  eapply (PiRedTmEq.eqApp Rtu ρ wfΔ hab).
Qed.

Lemma consWkEq {Δ Ξ F} σ (ρ : Δ ≤ Ξ) a Z : Z[up_term_term σ]⟨wk_up F[σ] ρ⟩[a..] = Z[a .: σ⟨ρ⟩].
Proof. bsimpl; cbn; now rewrite rinstInst'_term_pointwise. Qed.

Lemma eq_subst_3 t a ρ σ : t[up_term_term σ][a .: ρ >> tRel] = t[up_term_term σ⟨ρ⟩][a..].
Proof.
  bsimpl ; now substify.
Qed.

Lemma eq_subst_4 t a σ : t[up_term_term σ][a..] = t[a .: σ].
Proof.
  bsimpl ; now substify.
Qed.

Lemma eq_upren t σ ρ : t[up_term_term σ]⟨upRen_term_term ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. asimpl; unfold Ren1_subst; asimpl; substify; now asimpl. Qed.

Lemma eq_upren' {Γ Δ} A t σ (ρ : Δ ≤ Γ) : t[up_term_term σ]⟨wk_up A ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. eapply eq_upren. Qed.

Lemma eq_substren {Γ Δ} t σ (ρ : Γ ≤ Δ) : t[σ]⟨ρ⟩ = t[σ⟨ρ⟩].
Proof. now asimpl. Qed.

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
  eapply (Split_bind_return (validTyExt VΠFG wfΔ Vσσ')).
  intros Ξ wfΞ ρΞ oRVΠFG oRVΠFG'.
  rewrite 2subst_ren_wk.
  unshelve eapply wkSubst in Vσσ' as VσΞ; tea.
  assert ([Ξ ||-S< l > (tProd F G)[σ⟨ρΞ⟩] ≅ (tProd F' G')[σ'⟨ρΞ⟩]]) as SRΠFG by
    (rewrite <- 2subst_ren_wk; now eapply (validTyExt VΠFG wfΔ Vσσ')).
  instValid VσΞ.
  eapply (SirrLREq SRΠFG).
  1: symmetry; eapply subst_ren_wk.
  eapply Pi.canonPi_inv; refold; cbn.
  refine (Build_PiRedTmEq' (lamPiRedTm Vtt' VσΞ _) (lamPiRedTm' Vtt' VσΞ _) _ _).
  + pose proof (Vuσ := liftSubst' VF VσΞ).
    pose proof (Vuσ' := liftSubstSym' VF VσΞ).
    pose proof (symValidTm' Vtt'); pose proof (symValidTy' VG).
    instValid VσΞ; instValid Vuσ'; instValid Vuσ; escape.
    eapply lambda_cong; tea; now symmetry.
  + cbn -[Wpack]; refold; intros Θ ρΘ wfΘ *.
    set (RF := PolyRed.shpRed _ _ _) in hab.
    pose proof (VσΘ := wkSubst VΓ wfΞ wfΘ ρΘ VσΞ).
    pose proof (symValidTm' Vtt').
    instValid VσΘ; instValid (liftSubst' VF VσΘ); instValid (liftSubstSym' VF VσΘ).
    instValid (consWkSubstEq VF VσΞ ρΘ wfΘ (Wpack_return hab)).
    escape.
    eapply irrLREq.
(*     unshelve eapply Wpack_return'. cbn; refold. tea. intros. eapply SirrLR, SwkLR. *)
    1: symmetry; eapply eq_subst_3.
    eapply redSubstTmEq; cycle 1.
    * eapply redtm_beta; tea.
      now rewrite eq_upren, eq_substren.
    * eapply redtm_beta.
      1,3: rewrite eq_substren; tea.
      1: eapply ty_conv; tea; cbn; now rewrite eq_substren.
      now rewrite eq_upren, eq_substren.
      Unshelve. now rewrite 2!eq_subst_4.
    * now rewrite !eq_upren, !eq_subst_4.
  Qed.


Lemma lamValid {t t'} (Vtt' : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG]) :
  [Γ ||-v<l> tLambda F t : tProd F G | VΓ | VΠFG ].
Proof.
  now eapply lrefl, lamCongValid.
Qed.


Lemma singleSubst_subst_eq t a σ : t[a..][σ] = t[up_term_term σ][a[σ]..].
Proof. now bsimpl. Qed.

Lemma singleSubst_subst_eq' t a σ : t[a..][σ] = t[a[σ] .: σ].
Proof. now bsimpl. Qed.

Lemma betaValid {t t' a a'} (Vt : [Γ ,, F ||-v<l> t ≅ t' : G | VΓF | VG])
  (Va : [Γ ||-v<l> a ≅ a' : F | VΓ | VF]) :
  [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G[a..] | VΓ | substS VG Va].
Proof.
  eapply redSubstValid.
  2: now eapply lrefl, substSTm.
  constructor; intros; cbn.
  rewrite 2!singleSubst_subst_eq.
  instValid (lrefl Vσσ').
  instValid (liftSubst' VF (lrefl Vσσ')).
  escape; now eapply redtm_beta.
Qed.


Lemma redtm_app_helper {Δ Δ' f nf a σ} (ρ : Δ' ≤ Δ) :
  [|- Δ'] ->
  [Δ |- f[σ] ⤳* nf : (tProd F G)[σ]] ->
  [Δ' |- a : F[σ]⟨ρ⟩] ->
  [Δ' |- tApp f[σ]⟨ρ⟩ a ⤳* tApp nf⟨ρ⟩ a : G[up_term_term σ][a .: ρ >> tRel]].
Proof.
  intros red tya.
  rewrite eq_subst_3; eapply redtm_app; tea.
  eapply redtm_meta_conv; [now eapply redtm_wk| | reflexivity].
  cbn; now rewrite eq_upren.
Qed.


Lemma ηeqEqTermNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := (validTyExt VΠFG wfΔ Vσ))
   Ξ wfΞ (ρΞ : Ξ ≤ Δ) (oRΠFG : overtree RΠFG Ξ)
  (SRΠFG := (cover RΠFG Ξ wfΞ ρΞ oRΠFG))
  (RGσ : [Ξ ,, F[σ⟨ρΞ⟩] ||-<l> G[up_term_term σ⟨ρΞ⟩]])
  (Rf : [Ξ ||-S< l > f[σ]⟨ρΞ⟩ : (tProd F G)[σ]⟨ρΞ⟩ | LRPi' (normRedΠ SRΠFG) ]) :
  [RGσ | Ξ ,, F[σ⟨ρΞ⟩] ||- tApp f⟨ρ⟩[up_term_term σ⟨ρΞ⟩] (tRel 0) ≅
    tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ⟨ρΞ⟩]].
Proof.
  cbn in SRΠFG; revert Rf; refold; intros Rf.
  unshelve eapply wkSubst in Vσ as VσΞ; tea.
  pose (VσUp :=  liftSubst' VF VσΞ).
  instValid VσΞ; instValid VσUp; escape.
  assert (wfΞF : [|- Ξ,, F[σ⟨ρΞ⟩]]) by gen_typing.
  unshelve epose proof (r := eqApp' Rf wfΞF (@wk1 Ξ F[σ⟨ρΞ⟩]) (Svar0 _ _ _)); tea.
  1: cbn; symmetry; etransitivity; [eapply wk1_ren_on| eapply f_equal, subst_ren_wk ].
  eapply (dSplit_bind_return r).
  intros Θ wfΘ ρΘ or' or oRGσ.
  eapply SirrLREq; [ erewrite <-(var0_wk1_id (t:=G[_])); reflexivity|].
  eapply SredSubstLeftTmEq.
  + erewrite <- wk1_ren_on; eapply SirrLREq.
    2: now unshelve now eapply r.
    cbn. do 2 f_equal. eapply eq_upren.
  + clear dependent r; destruct Rf.(PiRedTmEq.redL) as [? [? red] ?]. cbn -[wk1 ren1] in *.
    replace f⟨ρ⟩[up_term_term σ⟨ρΞ⟩] with f[σ⟨ρΞ⟩]⟨@wk1 Ξ F[σ⟨ρΞ⟩]⟩.
    refine (redtm_wk ρΘ wfΘ _); clear dependent Θ.
    eapply redtm_app_helper; tea.
    1: now rewrite <- 2subst_ren_wk.
    1: rewrite wk1_ren_on; now eapply ty_var0.
    unfold ρ; now bsimpl.
    Unshelve.
    2: rewrite var0_wk1_id; now unshelve now eapply RGσ.
Qed.


Lemma ηeqEqTermConvNf {σ Δ f} (ρ := @wk1 Γ F)
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := (validTyExt VΠFG wfΔ Vσ))
   Ξ wfΞ (ρΞ : Ξ ≤ Δ) (oRΠFG : overtree RΠFG Ξ)
  (SRΠFG := (cover RΠFG Ξ wfΞ ρΞ oRΠFG))
  (Rf : [Ξ ||-<l> f[σ]⟨ρΞ⟩ : (tProd F G)[σ]⟨ρΞ⟩ | LRPi' (normRedΠ SRΠFG)]) :
  [Ξ ,, F[σ⟨ρΞ⟩] |- tApp f⟨ρ⟩[up_term_term σ⟨ρΞ⟩] (tRel 0) ≅
    tApp Rf.(PiRedTmEq.redR).(PiRedTmEq.nf)⟨↑⟩ (tRel 0) : G[up_term_term σ⟨ρΞ⟩]].
Proof.
  cbn in SRΠFG; revert Rf; refold; intros Rf.
  pose (VσUp :=  liftSubst' VF Vσ); instValid VσUp.
  unshelve eapply escapeSplitEqTerm, ηeqEqTermNf.
  eapply lrefl.
  rewrite <- subst_ren_wk, <- (eq_upren' F[σ]).
  eapply wkLRTy, RrVG.
  eapply wfc_cons, wft_wk; tea.
  instValid Vσ.
  now escape.
Qed.

Ltac normRedΠin Rt :=
  match type of Rt with
  | [LRAd.pack ?R | _ ||- ?t ≅ ?t' : _] =>
    apply (SirrLREq _ (LRPi' (normRedΠ R)) eq_refl) in Rt
  end; refold.


Lemma ηeqEqTerm {σ Δ f g} (ρ := @wk1 Γ F)
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ])
  (wfΔ : [|- Δ]) (Vσ : [Δ ||-v σ : Γ | VΓ| wfΔ])
  (RΠFG := validTyExt VΠFG wfΔ Vσ)
  (Rf : [Δ ||-<l> f[σ] : (tProd F G)[σ] | RΠFG ])
  (Rg : [Δ ||-<l> g[σ] : (tProd F G)[σ] | RΠFG ]) :
  [Δ ||-<l> f[σ] ≅ g[σ] : (tProd F G)[σ] | RΠFG ].
Proof.
  eapply (Split_bind Rf).
  intros Ξ wfΞ ρΞ oRf.
  eapply (Split_wk_bind_return Rg wfΞ ρΞ).
  intros Θ wfΘ ρΘ oRg oRΠFG.
  epose proof (Rf' := cover Rf Θ wfΘ (ρΘ∘w ρΞ) (overtree_PSh Rf oRf) oRΠFG); cbn in Rf'.
  epose proof (Rg' := cover Rg Θ wfΘ (ρΘ∘w ρΞ) oRg oRΠFG); cbn in Rg'.
  set (RΠ' := (cover RΠFG Θ wfΘ (ρΘ ∘w ρΞ) oRΠFG)) in *; cbn beta in RΠ'.
  eapply Pi.canonPi_inv. eapply Pi.canonPi in Rf', Rg'.
  set (RΠ := normRedΠ _) in *.
  revert RΠ Rf' Rg'; refold; intros.
  pose (Rf0 := Rf'.(PiRedTmEq.redR)); pose (Rg0 := Rg'.(PiRedTmEq.redR)).
  unshelve eapply wkSubst with (ρ:= ρΘ∘w ρΞ) in Vσ as VσΘ; tea.
  eapply (Build_PiRedTmEq' Rf0 Rg0).
  - cbn -[wk_well_wk_compose]; pose (VσUp := liftSubst' VF VσΘ).
    instValid VσΘ; instValid VσUp; escape.
    eapply convtm_eta; tea.
    4,6: eapply isLRFun_isWfFun; eapply PiRedTmEq.isfun.
    + now rewrite subst_ren_wk.
    + now rewrite subst_ren_wk, eq_upren.
    + destruct Rf0; cbn in *; gtyping.
    + destruct Rg0; cbn in *; gtyping.
    + rewrite subst_ren_wk, eq_upren.
      etransitivity ; [symmetry| etransitivity]; tea;
      eapply ηeqEqTermConvNf.
  - intros Ω ρΩ wfΩ ???.
    eassert ([ _ |Ω ||- a ≅ a : F[σ⟨ρΘ ∘w ρΞ⟩]⟨ρΩ⟩ ≅ _]) as haa by
      (eapply Wpack_return, SirrLREq, lrefl, hab; eapply f_equal, subst_ren_wk).
    epose (Vν := consWkSubstEq VF VσΘ ρΩ wfΩ haa); instValid Vν.
    assert (eq : forall t a τ, t⟨ρ⟩[a .: τ⟨ρΩ⟩] = t[τ]⟨ρΩ⟩) by (intros; unfold ρ; now bsimpl).
    cbn -[Wpack] in RVfg; rewrite 2!eq in RVfg.
    etransitivity; [| etransitivity].
    + symmetry; eapply redSubstLeftTmEq.
      1: pose proof (urefl (PiRedTmEq.eqApp Rf' ρΩ wfΩ (lrefl hab))); now eapply irrLREq.
      cbn -[wk_well_wk_compose]; rewrite eq_upren.
      eapply redtm_app_helper; tea; [| now escape].
      rewrite <- 2(subst_ren_wk (σ:=σ) (ρΘ ∘w ρΞ)).
      now destruct (PiRedTmEq.redR Rf') as [? []].
    + eapply irrLREq; tea. cbn -[wk_well_wk_compose]. now rewrite eq_upren, Poly.eq_subst_2.
    + eapply redSubstLeftTmEq.
      1: pose proof (rg := eqApp' Rg' wfΩ ρΩ hab); now eapply irrLREq.
      cbn -[wk_well_wk_compose]; rewrite eq_upren.
      eapply redtm_app_helper; tea; [| now escape].
      rewrite <- 2(subst_ren_wk (σ:=σ) (ρΘ ∘w ρΞ)).
      now destruct (PiRedTmEq.redL Rg') as [? []].
  Unshelve.
  eapply SwkLR. destruct RΠ, redL. cbn in *. clear - RΠ.
  eapply RΠ.
  Search ([_ ||-< _ > (tProd _ _)[_] ≅ _]).
  destruct RΠ, redL.
Qed.

Lemma etaeqValid {f g} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ])
  (Vg : [Γ ||-v<l> g : tProd F G | VΓ | VΠFG ])
  (Vfg : [Γ ,, F ||-v<l> tApp f⟨ρ⟩ (tRel 0) ≅ tApp g⟨ρ⟩ (tRel 0) : G | VΓF | VG ]) :
  [Γ ||-v<l> f ≅ g : tProd F G | VΓ | VΠFG].
Proof.
  constructor; intros ???? Vσ; instValid Vσ; instValid (lrefl Vσ).
  etransitivity.
  + eapply irrLREq; [reflexivity|];eapply ηeqEqTerm; tea.
  + now eapply irrLREq.
Qed.

Lemma etaExpandValid {f} (ρ := @wk1 Γ F)
  (Vf : [Γ ||-v<l> f : tProd F G | VΓ | VΠFG ]) :
  [Γ ,, F ||-v<l> eta_expand f : G | VΓF | VG].
Proof.
  unshelve epose (VF' := wkValidTy ρ _ _ VF); [|tea|].
  unshelve epose (wkValidTy ρ _ _ VΠFG); [|tea|].
  unshelve epose (wkValidTm ρ _ _ _ Vf); [|tea|].
  eapply irrValidTmRfl; cycle 1.
  + eapply appcongValid; erewrite <-wk1_ren_on.
    eapply irrValidTmRfl; tea; reflexivity.
  + refold; unfold ρ; now erewrite <-wk_up_ren_on, <-subst1_ren_wk_up, var0_wk1_id.
  Unshelve.
  1: tea.
  3: tea.
  all: refold.
  1: pose (var0Valid _ VF); now eapply irrValidTmRfl.
  tea.
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
  [Γ ||-v<l> (tLambda F (eta_expand f)) ≅ f : tProd F G | VΓ | VΠFG].
Proof.
  assert [||-v Γ,, F] by now eapply validSnoc.
  unshelve epose (wkValidTm ρ _ _ _ Vf); [|tea|].
  unshelve epose (VF' := wkValidTy ρ _ _ VF); [|tea|].
  unshelve epose (VG' := wkValidTy (wk_up F ρ) _ _ VG).
  2:now eapply validSnoc.
  unshelve epose (wkValidTy ρ _ _ VΠFG); [|tea|].
  eapply etaeqValid; tea.
  1: now eapply lamValid, etaExpandValid.
  unshelve epose (x := betaValid VF'  VG' (t:=(eta_expand f⟨ρ⟩)) (t':=(eta_expand f⟨ρ⟩)) (a:=(tRel 0)) (a':=(tRel 0)) _ _).
  3: eapply irrValidTmRfl; cycle 1.
  + eapply etaExpandValid; now eapply irrValidTmRfl.
  + pose (var0Valid _ VF); now eapply irrValidTmRfl.
  + cbn -[wk1] in x |- *.
    rewrite subst_rel0 in x.
    replace f⟨↑⟩⟨upRen_term_term (wk1 F)⟩ with f⟨ρ⟩⟨↑⟩.
    2: clear; unfold ρ; now bsimpl.
    apply x.
  + rewrite wk_up_wk1_ren_on; now bsimpl.
Qed.

End EtaValid.

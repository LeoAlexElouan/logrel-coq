From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly Pi Application.
From LogRel.Validity Require Import Validity Irrelevance Properties Pi Application Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Lemma isLRFun_isWfFun `{GenericTypingProperties}
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

Generalizable All Variables.

Lemma eta_expand'_one_subst `(ρ : Δ ≤ Γ) F t a : (eta_expand' Γ F t)⟨wk_up F ρ⟩[a..] = tApp t⟨ρ⟩ a.
Proof.
  now rewrite <- wk_app, to_subst_sound, <- subst_app,
    <- wk_up_wk1, <- to_subst_sound, shift_subst1.
Qed.

Section LambdaRed.
Context `{GenericTypingProperties}.

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

  Lemma eqApp' {Γ l A B} {ΠA : [Γ ||-Π< l > A ≅ B]} {t u}
    (Rtu : [Γ ||-Π t ≅ u : _ | ΠA]) 
    (nfL := PiRedTmEq.nf (PiRedTmEq.redL Rtu)) (nfR := PiRedTmEq.nf (PiRedTmEq.redR Rtu)):
    forall {Δ} wfΔ ρ {a b} (hab : [Δ ||-S< l > a ≅ b : _ | PolyRed.shpRed ΠA ρ wfΔ]),
    [Δ ||-< l > (tApp nfL⟨ρ⟩ a) ≅ (tApp nfR⟨ρ⟩ b) :_ | PolyRed.posRed ΠA ρ wfΔ hab].
  Proof.
    intros.
    eapply (PiRedTmEq.eqApp Rtu ρ wfΔ hab).
  Qed.


  Section Ext.

  Context `(RF : [Γ ||-< l > F ≅ F']).

  Definition LRExt G G' :=
    forall Δ `(wfΔ : [|-Δ]) (ρ : Δ ≤ Γ)
      `(Rab : [Δ ||-< l > a ≅ b : term_decl F⟨ρ⟩ | wkLRTy ρ wfΔ RF]),
      [Δ ||-< l > G⟨wk_up F ρ⟩[a..] ≅ G'⟨wk_up F' ρ⟩[b..]].

  #[global]Instance perExt : PER LRExt.
  Proof.
    constructor.
    + intros G G' eGG' ??????.
      symmetry; unshelve eapply eGG'; tea.
      symmetry; eapply Rab.
    + intros G G' G'' eGG' eG'G'' ??????.
      etransitivity; [unshelve eapply eGG' | unshelve eapply eG'G'']; tea.
      eapply urefl, Rab.
  Qed.

  Context (wfΓ : [|-Γ]).

  Let wfΓF : [|- Γ,, F ].
  Proof. now eapply wfc_cons; escape. Qed.
  Let wfΓF' : [|- Γ,, F' ].
  Proof. now eapply wfc_cons; escape. Qed.

  Lemma LRExtRed `(eGG' : LRExt G G') :
    [Γ,, F ||-< l > G ≅ G'].
  Proof.
    rewrite <- (@wk1_eta Γ F G), <- (@wk1_eta Γ F G').
    unshelve eapply eGG'; tea.
    now eapply var0.
  Qed.

  Lemma LRExtnow `(eGG' : LRExt G G') `(Rab : [Γ ||-S< l > a ≅ b : F | RF]) :
    [Γ ||-< l > G[a..] ≅ G'[b..]].
  Proof.
    replace G with G⟨wk_up F (@wk_id Γ)⟩.
    replace G' with G'⟨wk_up F' (@wk_id Γ)⟩.
    2,3 : now rewrite wk_up_wk_id, wk_id_ren_on.
    unshelve eapply eGG'; tea.
    eapply irrLREq, Rab.
    now rewrite wk_id_ren_on.
  Qed.

  Lemma LRExtRed' `(eGG' : LRExt G G') :
    [Γ,, F' ||-< l > G ≅ G'].
  Proof.
    rewrite <- (@wk1_eta Γ F' G), <- (@wk1_eta Γ F' G').
    unshelve eapply eGG'; tea.
    eapply var0conv, convty_wk, convty_equiv; escape; tea.
  Qed.


  Definition LRExtTm `(eGG' : LRExt G G') t t' := forall Δ `(wfΔ : [|-Δ]) (ρ : Δ ≤ Γ)
      `(Rab : [Δ ||-< l > a ≅ b : term_decl F⟨ρ⟩ | wkLRTy ρ wfΔ RF]),
      [Δ ||-< l > t⟨wk_up F ρ⟩[a..] ≅ t'⟨wk_up F' ρ⟩[b..] : _ | eGG' _ _ _ _ _ Rab].

  #[global]Instance perExtTm `(eGG' : LRExt G G') : PER (LRExtTm eGG').
  Proof.
    constructor.
    + intros t t' ett' ??????.
      symmetry.
      unshelve eapply irrLRConv, ett'; tea.
      { now symmetry. }
      set (eG := lrefl eGG').
      eapply eG, PER_Symmetric, Rab.
    + intros t t' t'' ett' et't'' ??????.
      etransitivity.
      - eapply ett'.
      - unshelve eapply irrLRConv, et't''; tea.
        { now eapply urefl. }
        set (eG := lrefl eGG').
        eapply eG, PER_Symmetric, Rab.
  Qed.

  Lemma LRExtTmRed `(eGG' : LRExt G G') `(ett' : LRExtTm eGG' t t') :
    [Γ,, F ||-< l > t ≅ t' : G | LRExtRed eGG' ].
  Proof.
    rewrite <- (@wk1_eta Γ F t), <- (@wk1_eta Γ F t').
    unshelve eapply irrLREq, ett'; tea.
    + now eapply var0.
    + now rewrite wk1_eta.
  Qed.

  Lemma LRExtTmRed' `(eGG' : LRExt G G') `(ett' : LRExtTm eGG' t t') :
    [Γ,, F' ||-< l > t ≅ t' : G | LRExtRed' eGG' ].
  Proof.
    rewrite <- (@wk1_eta Γ F' t), <- (@wk1_eta Γ F' t').
    unshelve eapply irrLREq, ett'; tea.
    + eapply var0conv, convty_wk; tea.
      now symmetry; escape.
    + change G⟨_⟩ with G⟨wk_up F (@wk1 Γ F)⟩. now rewrite wk1_eta.
  Qed.

  Lemma LRExtTmnow `(eGG' : LRExt G G') `(ett' : LRExtTm eGG' t t')
      `(Rab : [Γ ||-S< l > a ≅ b : F | RF]) :
    [Γ ||-< l > t[a..] ≅ t'[b..] : term_decl G[a..] | LRExtnow eGG' Rab].
  Proof.
    replace t with t⟨wk_up F (@wk_id Γ)⟩.
    replace t' with t'⟨wk_up F' (@wk_id Γ)⟩.
    2,3 : now rewrite wk_up_wk_id, wk_id_ren_on.
    unshelve eapply irrLREq, ett'; tea.
    2: now rewrite wk_up_wk_id, wk_id_ren_on.
    eapply irrLREq, Rab.
    now rewrite wk_id_ren_on.
  Qed.


  End Ext.

  Lemma irrLRExt {Γ l F F'} (RF RF' : [Γ ||-< l > F ≅ F' ]) `(eGG' : LRExt RF G G') :
    LRExt RF' G G'.
  Proof.
    intros ??????.
    unshelve eapply eGG', irrLR, Rab; tea.
  Qed.

  Lemma wkLRExt `(RF : [Γ ||-< l > F ≅ F']) {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) `(eGG' : LRExt RF G G') :
    LRExt (wkLRTy ρ wfΔ RF) G⟨wk_up F ρ⟩ G'⟨wk_up F' ρ⟩.
  Proof.
    intros Ξ wfΞ ρΞ ???.
    rewrite ! wk_comp_ren_on, (wk_up_wk_comp (A:=F) ρ),
      (wk_up_wk_comp (A:=F') ρ).
    unshelve eapply eGG', irrLREq, Rab; tea.
    now rewrite wk_comp_ren_on.
  Qed.

  Lemma irrLRExtTm {Γ l F F'} (RF RF' : [Γ ||-< l > F ≅ F' ]) `(eGG' : LRExt RF G G')
    (eGG'' : LRExt RF' G G') `(ett' : LRExtTm _ eGG' t t'):
      LRExtTm _ eGG'' t t'.
  Proof.
    intros ??????.
    unshelve eapply irrLR, ett'; tea.
    eapply irrLR, Rab.
  Qed.

  Lemma wkLRExtTm `(RF : [Γ ||-< l > F ≅ F']) {Δ} (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]) `(eGG' : LRExt RF G G')
    `(ett' : LRExtTm _ eGG' t t') :
    LRExtTm _ (wkLRExt _ ρ wfΔ eGG') t⟨wk_up F ρ⟩ t'⟨wk_up F' ρ⟩.
  Proof.
    intros Ξ wfΞ ρΞ ???.
    eapply irrLREq.
    shelve.
    rewrite ! wk_comp_ren_on, (wk_up_wk_comp (A:=F) ρ),
      (wk_up_wk_comp (A:=F') ρ).
    unshelve eapply ett'; tea.
    eapply irrLREq, Rab.
    now rewrite wk_comp_ren_on.
    Unshelve.
    now rewrite wk_comp_ren_on, <- wk_up_wk_comp.
  Qed.

  Section Strong.

  Context {Γ F F' G G' l} {wfΓ:[|-Γ]}
    {RF : [Γ ||-S< l > F ≅ F']}
    (eGG' : LRExt (WAd_return RF) G G').

  Let eG : LRExt (WAd_return RF) G G.
  Proof.
    eapply lrefl, eGG'.
  Qed.

  Let wfΓF : [|- Γ,, F ].
  Proof. now eapply wfc_cons; escape. Qed.
  Let wfΓF' : [|- Γ,, F' ].
  Proof. now eapply wfc_cons; escape. Qed.

  Let RGG' : [Γ,,F ||-< l > G ≅ G' ].
  Proof.
    now eapply LRExtRed, eGG'.
  Defined.
  Let RGG'' : [Γ,,F' ||-< l > G ≅ G' ].
  Proof.
    now eapply LRExtRed', eGG'.
  Defined.
  Lemma LambdaPiRed : [Γ ||-S< l > tProd F G ≅ tProd F' G'].
  Proof.
    eapply LRPi'.
    econstructor; escape.
    + constructor; [eapply redtywf_refl, wft_prod| |]; tea.
    + constructor; [eapply redtywf_refl, wft_prod| |]; tea.
    + tea.
    + now eapply convty_prod.
    + unshelve econstructor.
      - intros ?? wfΔ.
        now eapply SwkLR.
      - intros ????? Rab.
        now unshelve eapply eGG', Wpack_return', Rab.
  Qed.
  Let RΠFG := LambdaPiRed.

  Section Cong.

  Context `(ett' : LRExtTm _ eGG' t t').

  Let et : LRExtTm _ eGG' t t.
  Proof. eapply lrefl, ett'. Qed.

  Let et' : LRExtTm _ eGG' t' t'.
  Proof. eapply urefl, ett'. Qed.


  Let Rtt' : [Γ,,F ||-< l > t ≅ t' : G | RGG' ].
  Proof.
    now eapply LRExtTmRed.
  Qed.
  Let Rtt'' : [Γ,,F' ||-< l > t ≅ t' : G | RGG'' ].
  Proof.
    now eapply LRExtTmRed'.
  Qed.

  Lemma lamPiRedTm :
    PiRedTm (normRedΠ RΠFG) (tLambda F t).
  Proof.
    set (R := normRedΠ RΠFG).
    exists (tLambda F t).
    1: now escape; eapply redtmwf_refl, ty_lam.
    eapply LamLRFun'; escape; tea; [now eapply lrefl|].
    intros ????? Rab.
    set (RFwk := PolyRed.shpRed R ρ wfΔ : [Δ ||-S< l > F⟨ρ⟩ ≅ F'⟨ρ⟩]) in *.
    change (ParamRedTy.domL R) with F.
    change (ParamRedTy.domR R) with F'.
    change (ParamRedTy.codL R) with G.
    change (ParamRedTy.codR R) with G'.
    unshelve eapply irrLR, et; tea.
    eapply Wpack_return', Rab.
  Defined.

  Lemma lamPiRedTm' :
    PiRedTm (normRedΠ RΠFG) (tLambda F' t').
  Proof.
    set (R := normRedΠ RΠFG).
    exists (tLambda F' t').
    { escape. eapply redtmwf_refl, ty_conv.
      + eapply ty_lam; tea.
      + eapply convty_prod; tea.
        - now symmetry.
        - now etransitivity; [|symmetry]. }
    eapply LamLRFun'; escape ;tea.
    intros ????? Rab.
    set (RFwk := PolyRed.shpRed R ρ wfΔ : [Δ ||-S< l > F⟨ρ⟩ ≅ F'⟨ρ⟩]) in *.
    change (ParamRedTy.domL R) with F.
    change (ParamRedTy.domR R) with F'.
    change (ParamRedTy.codL R) with G.
    change (ParamRedTy.codR R) with G'.
    unshelve eapply irrLR, et'; tea.
    eapply Wpack_return', Rab.
  Defined.


  Lemma SlamCongRed :
    [Γ ||-S<l> tLambda F t ≅ tLambda F' t' : tProd F G | RΠFG ].
  Proof.
    eapply canonPi_inv.
    unshelve eapply Pi.Build_PiRedTmEq'.
    { eapply lamPiRedTm. }
    { eapply lamPiRedTm'. }
    + cbn. unshelve (eapply lambda_cong; try (escape; eassumption)).
      1,2: now eapply lrefl; escape.
    + intros ????? Rab.
      unfold lamPiRedTm, lamPiRedTm';
        cbn [PiRedTmEq.nf].
      rewrite <-! wk_lam.
      eapply redSubstTmEq.
      2,3: eapply redtm_beta.
      3: refine (ty_wk (A:=G) _ (wfc_cons wfΔ _) _).
      7: refine (ty_wk (A:=G') _ (wfc_cons wfΔ _) _).
      2,3,6,7 : eapply wft_wk; tea.
      2-9: escape; tea.
      - unshelve eapply irrLR, ett'; tea.
        eapply Wpack_return', Rab.
      - eapply ty_conv; tea.
      - eapply ty_conv, convty_wk; tea.
  Qed.

  Let eGG'now : forall `(Rab : [Γ ||-S< l > a ≅ b : F | RF]),
      [Γ ||-< l > G[a..] ≅ G'[b..]].
  Proof.
    intros.
    eapply LRExtnow.
    - tea.
    - eapply eGG'.
    - eapply Wpack_return', Rab.
  Defined.

  Let ett'now : forall `(Rab : [Γ ||-S< l > a ≅ b : F | RF]),
      [Γ ||-< l > t[a..] ≅ t'[b..] : _ | eGG'now Rab].
  Proof.
    intros.
    eapply LRExtTmnow, ett'.
  Qed.

  Lemma SbetaRed `(Rab : [Γ ||-S< l > a ≅ b : F | RF]) :
    [Γ ||-< l > tApp (tLambda F t) a ≅ t[a..] : term_decl G[a..] | eGG'now Rab].
  Proof.
    eapply redSubstLeftTmEq.
    2: eapply redtm_beta; now escape.
    eapply lrefl, ett'now.
  Qed.

  End Cong.

  Section Eta.

  Lemma etaNfRed `(Rt : [Γ ||-S< l > t : _ | RΠFG]) :
    [Γ,, F ||-< l > eta_expand' Γ F t ≅
      eta_expand' Γ F (canonPi Rt).(PiRedTmEq.redL).(PiRedTmEq.nf) : _ | RGG'].
  Proof.
    set (Πt := canonPi Rt).
    destruct Πt.
    eapply redSubstLeftTmEq.
    + cbn delta iota.
      unshelve eapply PER_Symmetric, irrLREq, eqApp.
      shelve.
      - tea.
      - eapply Svar0; now escape.
      - eapply wk1_eta.
    + rewrite <- (@wk1_eta Γ F G).
      eapply redtm_app, ty_var; tea.
      - rewrite wk_prod.
        eapply redtm_wk; tea.
        eapply redR.
      - eapply in_here'.
  Qed.

  Context `(ett' : LRExtTm _ eGG' (eta_expand' Γ F t) (eta_expand' Γ F t')).

  Lemma SetaeqRed
    (Rt : [Γ ||-S< l > t : _ | RΠFG])
    (Rt' : [Γ ||-S< l > t' : _ | RΠFG]) :
    [Γ ||-S< l > t ≅ t' : _ | RΠFG].
  Proof.
    set (Πt := canonPi Rt).
    set (Πt' := canonPi Rt').
    unshelve eapply canonPi_inv, Build_PiRedTmEq'.
    + eapply Πt.
    + eapply Πt'.
    + eapply convtm_eta.
      - now escape.
      - now escape.
      - now destruct Πt as [[nft []]].
      - destruct Πt as [[nft []]].
        now eapply isLRFun_isWfFun.
      - now destruct Πt' as [[nft' []]].
      - destruct Πt' as [[nft' []]].
        now eapply isLRFun_isWfFun.
      - cbn.
        etransitivity; [etransitivity|].
        3 : eapply escapeSplitTm, etaNfRed.
        1: symmetry; eapply escapeSplitTm, etaNfRed.
        now unshelve eapply escapeSplitTm, LRExtTmRed, ett'.
    + intros ????? Rab.
      cbn zeta.
      etransitivity; [symmetry | etransitivity]; cycle 2.
      - destruct Πt' as [[nft' []]].
        eapply redSubstLeftTmEq.
        cbn delta iota.
        1:{ unshelve eapply lrefl, irrLRConv, eqApp.
          + shelve.
          + tea.
          + now eapply urefl.
          + now unshelve eapply eG, PER_Symmetric,
            Wpack_return', Rab. }
        eapply redtm_conv.
        * eapply redtm_app.
          2: now escape.
          erewrite wk_prod.
          eapply redtm_wk; tea.
        * now unshelve eapply escapeSplitTy, eG, PER_Symmetric,
            Wpack_return', Rab.
      - destruct Πt as [[nft []]].
        eapply redSubstLeftTmEq.
        1: now unshelve eapply lrefl, irrLR, eqApp.
        eapply redtm_app.
        1: now rewrite wk_prod; eapply redtm_wk.
        now escape.
      - replace (tApp _ _) with (eta_expand' Γ F t)⟨wk_up F ρ⟩[a..].
        replace (tApp _ b) with (eta_expand' Γ F t')⟨wk_up F ρ⟩[b..].
        2-3: rewrite <- wk_app, to_subst_sound, <- subst_app;
          f_equal;
          now rewrite <- wk_up_wk1, <- to_subst_sound, shift_subst1.
        unshelve eapply irrLR, ett'; tea.
        eapply Wpack_return', Rab.
  Qed.

(*   Context {t t'}
    (Rtt'ext : forall `(wfΔ : [|-Δ]) (ρ : Δ ≤ Γ)
      `(Rab : [Δ ||-< l > a ≅ b : term_decl F⟨ρ⟩ | wkLRTy ρ wfΔ (WAd_return RF)]),
      [Δ ||-< l > tApp t⟨ρ⟩ a ≅ tApp t'⟨ρ⟩ b : _ | eGG' _ _ _ _ _ Rab]).

  Lemma SetaeqRed
    (Rt : [Γ ||-S< l > t : _ | RΠFG])
    (Rt' : [Γ ||-S< l > t' : _ | RΠFG]) :
    [Γ ||-S< l > t ≅ t' : _ | RΠFG].
  Proof.
    set (Πt := canonPi Rt).
    set (Πt' := canonPi Rt').
    unshelve eapply canonPi_inv, Build_PiRedTmEq'.
    + eapply Πt.
    + eapply Πt'.
    + eapply convtm_eta.
      - now escape.
      - now escape.
      - now destruct Πt as [[nft []]].
      - destruct Πt as [[nft []]].
        now eapply isLRFun_isWfFun.
      - now destruct Πt' as [[nft' []]].
      - destruct Πt' as [[nft' []]].
        now eapply isLRFun_isWfFun.
      - cbn.
        etransitivity; [etransitivity|].
        3 : eapply escapeSplitTm, etaNfRed.
        1: symmetry; eapply escapeSplitTm, etaNfRed.
        rewrite <- (@wk1_eta Γ F G).
        unshelve eapply escapeSplitTm, Rtt'ext; tea.
        now eapply var0.
    + intros ????? Rab.
      cbn zeta.
      etransitivity; [symmetry | etransitivity].
      - destruct Πt as [[nft []]].
        eapply redSubstLeftTmEq.
        1: now unshelve eapply lrefl, irrLR, eqApp.
        eapply redtm_app.
        1: now rewrite wk_prod; eapply redtm_wk.
        now escape.
      - unshelve eapply irrLR, Rtt'ext; [shelve|tea|].
        eapply Wpack_return', Rab.
      - destruct Πt' as [[nft' []]].
        eapply redSubstLeftTmEq.
        cbn delta iota.
        1:{ unshelve eapply lrefl, irrLRConv, eqApp.
          + shelve.
          + tea.
          + now eapply urefl.
          + now unshelve eapply eG, PER_Symmetric,
            Wpack_return', Rab. }
        eapply redtm_conv.
        * eapply redtm_app.
          2: now escape.
          erewrite wk_prod.
          eapply redtm_wk; tea.
        * now unshelve eapply escapeSplitTy, eG, PER_Symmetric,
            Wpack_return', Rab.
  Qed. *)

  End Eta.

  End Strong.

Lemma RedΠdom  {Γ F F' G G' l} {wfΓ:[|-Γ]}
    (RΠFG : [Γ ||-S< l > tProd F G ≅ tProd F' G']) :
    [Γ ||-S< l > F ≅ F'].
Proof.
  rewrite <- (wk_id_ren_on Γ), <- (wk_id_ren_on Γ F).
  now eapply (normRedΠ RΠFG).(ParamRedTy.polyRed).(PolyRed.shpRed).
Qed.

  Section Weak.

  Section Early.

  Context {Γ F F' G G' l} {wfΓ:[|-Γ]}
    {RF : [Γ ||-< l > F ≅ F']}
    (eGG' : LRExt RF G G').

  Lemma LRExtProd : [Γ ||-< l > tProd F G ≅ tProd F' G'].
  Proof.
    eapply (Split_bind_return RF).
    intros Δ wfΔ ρ oRF.
    rewrite <-! wk_prod.
    unshelve eapply LambdaPiRed; tea.
    + now eapply RF.
    + intros Ξ wfΞ ρΞ a b Rab.
      rewrite ! wk_decl,
        ! wk_comp_ren_on, ! wk_up_wk_comp.
      unshelve eapply eGG'; tea.
      eapply irrLREq, Rab.
      now rewrite wk_comp_ren_on.
  Qed.

  Let RΠFG := LRExtProd.

  Section Cong.

  Context `(ett' : LRExtTm _ eGG' t t').

  Lemma lamCongRed :
    [Γ ||-<l> tLambda F t ≅ tLambda F' t' : tProd F G | RΠFG ].
  Proof.
    eapply (Split_bind_return RF).
    intros ??? oRf oRΠFG.
    rewrite <-! wk_lam.
    unshelve eapply SirrLREq, SlamCongRed.
    + exact G⟨wk_up F ρ⟩.
    + exact G'⟨wk_up F' ρ⟩.
    + tea.
    + now eapply RF.
    + now unshelve eapply irrLRExt, wkLRExt, eGG'.
    + now rewrite <- wk_prod.
    + now unshelve eapply irrLRExtTm, wkLRExtTm, ett'.
  Qed.


  Let eGG'now : forall `(Rab : [Γ ||-< l > a ≅ b : F | RF]),
      [Γ ||-< l > G[a..] ≅ G'[b..]].
  Proof.
    intros ???.
    now eapply LRExtnow, Rab.
  Defined.

  Let ett'now : forall `(Rab : [Γ ||-< l > a ≅ b : F | RF]),
      [Γ ||-< l > t[a..] ≅ t'[b..] : _ | eGG'now Rab].
  Proof.
    intros.
    eapply LRExtTmnow, ett'.
  Qed.

  Let Rtt' : [Γ,,F ||-< l > t ≅ t' : G | LRExtRed _ wfΓ eGG' ].
  Proof.
    now eapply LRExtTmRed.
  Qed.


(*   Lemma betaRed' : LRExtTm _ eGG' (eta_expand' Γ F (tLambda F t)) t'.
  Proof.
    intros ??????.
    rewrite eta_expand'_one_subst, <- wk_lam.
    eapply redSubstLeftTmEq.
    eapply ett'.
    eapply redtm_beta; escape; tea.
    gtyping.
    refine (ty_wk (wk_up F ρ) _ EscLRtt').
    rewrite <- wk_decl.
    eapply wfc_cons. tea.
    eapply wft_wk; tea.
  Qed. *)


  Lemma betaRed `(Rab : [Γ ||-< l > a ≅ b : F | RF]) :
    [Γ ||-< l > tApp (tLambda F t) a ≅ t[a..] : term_decl G[a..] | eGG'now Rab].
  Proof.
    eapply redSubstLeftTmEq.
    2: eapply redtm_beta; escape; tea.
    eapply lrefl, ett'now.
  Qed.

  End Cong.


  Lemma etaeqRed `(ett' : LRExtTm _ eGG' (eta_expand' Γ F t) (eta_expand' Γ F t'))
    (Rt : [Γ ||-< l > t : _ | RΠFG])
    (Rt' : [Γ ||-< l > t' : _ | RΠFG]) :
    [Γ ||-< l > t ≅ t' : _ | RΠFG].
  Proof.
    eapply (dSplit_bind Rt).
    intros ??? _ oRt.
    unshelve eapply (dSplit_wk_bind_return Rt'); tea.
    intros ??? _ oRt' oRΠ.
    unshelve eapply SirrLREq, SetaeqRed.
    - exact F⟨ρΞ ∘w ρ⟩.
    - exact F'⟨ρΞ ∘w ρ⟩.
    - exact G⟨wk_up F (ρΞ ∘w ρ)⟩.
    - exact G'⟨wk_up F' (ρΞ ∘w ρ)⟩.
    - tea.
    - eapply RedΠdom.
      erewrite ! wk_prod.
      now eapply RΠFG, oRΠ.
      Unshelve. tea.
    - now unshelve eapply irrLRExt, wkLRExt, eGG'. Unshelve.
    - now rewrite wk_prod.
    - replace (tApp t⟨_⟩⟨_⟩ _)
        with (eta_expand' Γ F t)⟨wk_up F (ρΞ ∘w ρ)⟩.
      replace (tApp t'⟨_⟩⟨_⟩ _)
        with (eta_expand' Γ F' t')⟨wk_up F' (ρΞ ∘w ρ)⟩.
      2-3: now rewrite <- wk_app, <- wk_up_wk1.
      now unshelve eapply irrLRExtTm, wkLRExtTm, ett'.
    - unshelve eapply SirrLREq, Rt, overtree_PSh; tea.
      now rewrite wk_prod.
    - unshelve eapply SirrLREq, Rt'; tea.
      now rewrite wk_prod.
  Qed.

  End Early.

  Context {Γ F F' G G' l} {wfΓ:[|-Γ]}
    {RF : [Γ ||-< l > F ≅ F']}
    (eGG' : LRExt RF G G').


  Lemma etaRed {t t'}
    (ett' : LRExtTm _ eGG' (eta_expand' Γ F t) (eta_expand' Γ F' t'))
    (Rt : [Γ ||-< l > t : _ | LRExtProd eGG' ]) :
    [Γ ||-< l > tLambda F (eta_expand' Γ F t) ≅ t : _ | LRExtProd eGG'].
  Proof.
    eapply etaeqRed, Rt.
    + intros ??????.
      rewrite eta_expand'_one_subst, <- wk_lam.
      etransitivity.
      unshelve eapply irrLR, betaRed, wkLRExtTm, ett'; tea.
      eapply lrefl in ett' as et.
      eapply et.
    + eapply lrefl, lamCongRed, ett'.
  Qed.

  End Weak.

  End LambdaRed.
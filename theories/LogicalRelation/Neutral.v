From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.
From LogRel.LogicalRelation Require Import Induction Escape Irrelevance Symmetry Transitivity.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Neutral.
Context `{GenericTypingProperties}.

Definition neu {l Γ A B} : [Γ |- A] -> [Γ |- B] -> [ Γ |- A ~ B : U] -> [Γ ||-S<l> A ≅ B].
Proof.
  intros; apply LRne_.
  exists A B ; tea; gtyping.
Defined.

Lemma neU {l l' Γ A B n n'} (h : [Γ ||-U<l> A ≅ B]) :
  [Γ |- n : A] ->
  [Γ |- n ~ n' : A] ->  URedTm l' Γ n.
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros; exists n.
  * eapply redtmwf_conv; tea; now eapply redtmwf_refl.
  * now eapply NeType, convneu_whne.
Defined.

Definition reflect {l Γ A B} (RA : [Γ ||-S<l> A ≅ B]) :=
 forall n n',
    [Γ |- n : A] ->
    [Γ |- n' : A] ->
    [Γ |- n ~ n' : A] ->
    [Γ ||-S<l> n ≅ n' : _ | RA].


Lemma reflect_diag {l Γ A B} (RA : [Γ ||-S<l> A ≅ B]) (c : reflect RA) :
  forall n, [Γ |- n : A] -> [Γ |- n ~ n : A] -> [Γ ||-S<l> n : A | RA].
Proof.
  intros; eapply c.
  all: eassumption.
Qed.

Lemma reflect_var0 {l Γ A A' B'} (RA : [Γ ,, A ||-S<l> A' ≅ B']) :
  reflect RA ->
  [Γ ,, A |- A⟨@wk1 Γ A⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-S<l> tRel 0 : A' | RA].
Proof.
  intros cRA conv HA.
  assert [Γ ,, A |- tRel 0 : A'].
  1:{
    eapply ty_conv; tea; escape.
    rewrite wk1_ren_on.
    unshelve eapply (ty_var _ (in_here _ _ : in_ctx (Γ,,A) 0 A⟨↑⟩)).
    now eapply wfc_wft.
  }
  eapply reflect_diag; tea.
  eapply convneu_var; tea.
Qed.


Lemma reflect_U {l Γ A B} (h : [Γ ||-U<l> A ≅ B]) : reflect (LRU_ h).
Proof.
  assert [Γ |- A ≅ U] by (destruct h; gen_typing).
  intros n n' tyn tyn' conv.
  exists (neU h tyn conv) (neU h tyn' (symmetry conv)).
  * cbn; eapply convtm_convneu; [constructor|]; now eapply convneu_conv.
  * eapply redTyRecBwd, neu.
    1,2: gtyping.
    now eapply convneu_conv.
Qed.


Lemma reflect_ne {l Γ A B} (RA : [Γ ||-ne A ≅ B]) : reflect (LRne_ l RA).
Proof.
  intros ? **. pose proof (h := whredL_conv (LRne_ l RA)); cbn in h.
  exists n n'; cbn.
  1,2: eapply redtmwf_refl ; eapply ty_conv; gen_typing.
  gen_typing.
Qed.


Section ReflectPi.
Context {l Γ A B} (RA : [Γ ||-Π< l > A ≅ B]).

Let convΠ : [Γ |- A ≅ outTyL RA] := whredL_conv (LRPi' RA).

#[local]
Definition funred {n} : [Γ |- n : A] -> [Γ |- n ~ n : A] -> PiRedTm RA n.
Proof.
  intros. exists n; cbn.
  - now eapply redtmwf_refl, ty_conv.
  - constructor; now eapply convneu_conv.
Defined.


Lemma reflect_Pi
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        dover (PolyRed.posRed RA ρ h ha) (fun _ _ _ => reflect))
  : reflect (LRPi' RA).
Proof.
  destruct (ParamRedTy.redL RA).
  intros ?? hn hn' hnn'.
  pose proof (lrefl hnn') as hnn; pose proof (urefl hnn') as hn'n'.
  unshelve econstructor.
  1,2: now apply funred.
  * cbn; eapply convtm_eta ; tea.
    1-4: first [now eapply ty_conv| constructor; now eapply convneu_conv].
    rewrite <-(@wk1_eta Γ RA.(ParamRedTy.domL) RA.(ParamRedTy.codL)).
    assert [Γ,, PiRedTy.domL RA |-[ ta ] tRel 0 : (PiRedTy.domL RA)⟨@wk1 Γ (PiRedTy.domL RA)⟩]
      as h0
      by ( eapply ty_var0; now destruct RA as [???? []]).
    assert [|- Γ,, PiRedTy.domL RA] as hΓA by gtyping.
    eassert ([PolyRed.shpRed RA (wk1 _) hΓA | _ ||- tRel 0 ≅ tRel 0 : _]) as hvar0.
    1: { eapply reflect_diag.
      eapply ihdom.
      2: eapply convneu_var.
      all: eapply h0. }
    eapply (Split_bind_convtm (PolyRed.posRed RA (wk1 _) hΓA hvar0 )); tea.
    intros Δ wfΔ ρ ohvar0.
    unshelve eapply escapeTm, ihcod.
    5 : apply ohvar0.
    1 : apply wfΔ.
    + apply ty_wk; [tea|].
      eapply ty_app_ren; tea.
    + apply ty_wk; [tea|].
      eapply ty_app_ren; tea.
    + apply convneu_wk; [tea|].
      eapply convneu_app_ren; tea.
      eapply escapeTm, ihdom; tea; now apply convneu_var.
      Unshelve. all:gtyping.
  * intros Δ a b ρ hΔ hab.
    eapply Split_return; tea.
    intros Ξ wfΞ ρΞ ohab; cbn in ohab, hab.
    escape.
    apply ihcod.
    + now eapply ty_wk, ty_app_ren.
    + eapply (ty_wk _ wfΞ), ty_conv; clear Ξ wfΞ ρΞ ohab.
      now eapply ty_app_ren.
      unshelve epose proof (kripkeLRlrefl (PolyRed.posRed RA) ρ hΔ hab) as hcod.
      symmetry.
      now escape.
    + eapply convneu_wk; tea.
      eapply convneu_app_ren.
      1,2: eassumption.
      now escape.
Qed.

End ReflectPi.

Section ReflectSig.
Context {l Γ A B} (RA : [Γ ||-Σ< l > A ≅ B]).

Let convΣ : [Γ |- A ≅ outTyL RA] := whredL_conv (LRSig' RA).

#[local]
Definition sigred {n} : [Γ |- n : A] -> [Γ |- n ~ n : A] -> SigRedTm RA n.
Proof.
  intros. exists n; cbn.
  - now eapply redtmwf_refl, ty_conv.
  - constructor; now eapply convneu_conv.
Defined.

#[local]
Definition hconv_fst
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  {n n' Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ])  :
  [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] ->
  [PolyRed.shpRed RA ρ h | Δ ||- tFst n⟨ρ⟩ ≅ tFst n'⟨ρ⟩ : _].
Proof.
  intros; eapply ihdom; rewrite !wk_fst.
  1,2: eapply ty_wk; tea; now eapply ty_fst, ty_conv.
  eapply convneu_wk; tea; now eapply convneu_fst, convneu_conv.
Qed.

#[local]
Definition hconv_snd
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        dover (PolyRed.posRed RA ρ h ha) (fun _ _ _ => reflect))
  {n n' Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ])
  (tyn : [Γ |- n : A]) (tyn' : [Γ |- n' : A]) (convnn' : [Γ |- n ~ n' : A])
  (hfst := hconv_fst ihdom ρ h tyn tyn' convnn') :
  dover (PolyRed.posRed RA ρ h hfst) (fun Ξ _ ρΞ hSplit => [ hSplit | Ξ ||- tSnd n⟨ρ⟩⟨ρΞ⟩ ≅ tSnd n'⟨ρ⟩⟨ρΞ⟩ : _]).
Proof.
  intros Ξ wfΞ ρΞ ohfst; eapply ihcod; rewrite !wk_fst, !wk_snd, <- subst_ren_wk_up.
  1,2: eapply ty_wk; tea.
  * now eapply ty_wk, ty_snd, ty_conv.
  * eapply ty_wk, ty_conv; tea; clear Δ ρ h hfst Ξ wfΞ ρΞ ohfst.
    1: now eapply ty_snd, ty_conv.
    assert (wfΓ : [|-Γ]) by gtyping.
    pose (hfst' := hconv_fst ihdom wk_id wfΓ tyn tyn' convnn').
    unshelve epose proof (kr := kripkeLRlrefl (PolyRed.posRed RA) wk_id wfΓ hfst'); tea.
    rewrite wk_up_wk_id, 3 wk_id_ren_on in kr; symmetry.
    unshelve eapply Split_bind_convty; tea.
    intros Δ ρ hover hΔ.
    now eapply escapeTy, kr.
  * do 2 (eapply convneu_wk; tea); now eapply convneu_snd, convneu_conv.
Qed.

Lemma reflect_Sig
  (ihdom : forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]),
        reflect (PolyRed.shpRed RA ρ h))
  (ihcod : forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
          (ha : [PolyRed.shpRed RA ρ h | Δ ||- a ≅ b: _]),
        dover (PolyRed.posRed RA ρ h ha) (fun _ _ _ => reflect))
  : reflect (LRSig' RA).
Proof.
  destruct (ParamRedTy.redL RA).
  intros ???? h.
  pose proof (lrefl h); pose proof (urefl h).
  unshelve econstructor.
  1,2: now apply sigred.
  * intros; now eapply hconv_fst.
  * assert (wfΓ : [|-Γ]) by gtyping.
    unshelve epose proof (hfst := hconv_fst ihdom wk_id wfΓ _ _ h); tea.
    unshelve epose proof (hsnd := hconv_snd ihdom ihcod wk_id wfΓ _ _ h); tea.
    unshelve eapply (Split_bind_convtm (PolyRed.posRed RA wk_id wfΓ (hconv_fst ihdom wk_id wfΓ H8 H9 h))); tea.
    intros Δ wfΔ ρ ohconv_fst.
    specialize (hsnd Δ wfΔ ρ ohconv_fst).
    cbn in hsnd; escape.
    rewrite !wk_up_wk_id, !wk_id_ren_on in *.
    unfold sigred, SigRedTyPack.outTy; cbn[SigRedTmEq.nf].
    rewrite <- wk_sig.
    apply convtm_eta_sig; tea.
    + now eapply wft_wk.
    + eapply wft_wk, codTy.
      eapply wfc_cons, wft_wk, domTy; tea.
    + rewrite wk_sig.
      eapply ty_wk ; tea.
      now eapply ty_conv.
    + constructor.
      rewrite wk_sig.
      eapply convneu_wk; tea.
      now eapply convneu_conv.
    + rewrite wk_sig.
      eapply ty_wk ; tea.
      now eapply ty_conv.
    + constructor.
      rewrite wk_sig.
      eapply convneu_wk; tea.
      now eapply convneu_conv.
    + rewrite 2 wk_fst.
      eapply convtm_wk; tea.
    + now rewrite wk_fst, <- subst_ren_wk_up.
  * intros Δ ρ hΔ.
    eapply Split_return; tea.
    intros Ξ wfΞ ρΞ ofst.
    eapply hconv_snd.
    clear dependent Δ; clear dependent Ξ.
    eapply ihcod.
Qed.
End ReflectSig.

Lemma reflect_Nat {l Γ A B} (NA : [Γ ||-Nat A ≅ B]) : reflect (LRNat_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LRNat_ l NA)).
  assert [Γ |- n : tNat] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  1,3: eapply convneu_conv; [|eassumption]; tea.
  eapply ty_conv; eassumption.
Qed.

Lemma reflect_Bool {l Γ A B} (NA : [Γ ||-Bool A ≅ B]) : reflect (LRBool_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LRBool_ l NA)).
  assert [Γ |- n : tBool] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  1,3: eapply convneu_conv; [|eassumption]; tea.
  eapply ty_conv; eassumption.
Qed.

Lemma reflect_Empty {l Γ A B} (NA : [Γ ||-Empty A ≅ B]) : reflect (LREmpty_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LREmpty_ l NA)).
  assert [Γ |- n : tEmpty] by now eapply ty_conv.
  assert [Γ |- n' : tEmpty] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  constructor; tea; now eapply convneu_conv.
Qed.

Lemma reflect_Tree {l Γ A B} (NA : [Γ ||-Tree A ≅ B]) : reflect (LRTree_ l NA).
Proof.
  red; intros; pose proof (whredL_conv (LRTree_ l NA)).
  assert [Γ |- n : tTree] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  1,3: eapply convneu_conv; [|eassumption]; tea.
  eapply ty_conv; eassumption.
Qed.

Lemma reflect_Id {l Γ A B} (IA : [Γ ||-Id<l> A ≅ B]) :
  reflect (LRId' IA).
Proof.
  red; intros; pose proof (whredL_conv (LRId' IA)).
  assert [Γ |- n : IdRedTy.outTy IA] by now eapply ty_conv.
  assert [Γ |- n' : IdRedTy.outTy IA] by now eapply ty_conv.
  econstructor.
  1,2: eapply redtmwf_refl; tea; now eapply ty_conv.
  2: do 2 constructor; tea.
  1: eapply convtm_convneu ; [now constructor|..].
  all: now eapply convneu_conv.
Qed.

Lemma reflectLR {l Γ A B} (RA : [Γ ||-S<l> A ≅ B]) : reflect RA.
Proof.
  indLR RA; intros.
  - now apply reflect_U.
  - now apply reflect_ne.
  - now apply reflect_Pi.
  - now apply reflect_Nat.
  - now apply reflect_Bool.
  - now apply reflect_Empty.
  - now apply reflect_Tree.
  - now apply reflect_Sig.
  - now apply reflect_Id.
Qed.

Definition neuTerm {l Γ A B} (RA : [Γ ||-S<l> A ≅ B]) {n} :=
  reflect_diag RA (reflectLR RA) n.

Lemma SneNfTermEq {Γ l A n n'} (RA : [Γ ||-S<l> A]) : [Γ ||-NeNf n ≅ n' : A] -> [RA | Γ ||- n ≅ n' : A].
Proof. intros []; now eapply reflectLR. Qed.


Lemma Svar0conv {l Γ A A' B'} (RA : [Γ ,, A ||-S<l> A' ≅ B']) :
  [Γ,, A |- A⟨@wk1 Γ A⟩ ≅ A'] ->
  [Γ |- A] ->
  [Γ ,, A ||-S<l> tRel 0 : A' | RA].
Proof.
  apply reflect_var0 ; now eapply reflectLR.
Qed.

Lemma Svar0 {l Γ A A' B'} (RA : [Γ ,, A ||-S<l> A' ≅ B']) :
  A⟨@wk1 Γ A⟩ = A' ->
  [Γ |- A] ->
  [Γ ,, A ||-S<l> tRel 0 : A' | RA].
Proof.
  intros; subst; apply Svar0conv; tea.
  eapply lrefl; now escape.
Qed.


Lemma neNfTermEq {Γ l A n n'} (RA : [Γ ||-<l> A]) :
  [Γ ||-NeNf n ≅ n' : A] -> [RA | Γ ||- n ≅ n' : A].
Proof.
  intros [Hn Hn' Hnn'].
  eapply Split_return.
  1: escape; gtyping.
  intros Δ wfΔ ρ oRA.
  eapply SneNfTermEq; constructor;
  now first [eapply ty_wk|eapply convneu_wk].
Qed.

Lemma var0conv {l Γ A A' B'} (RAB : [ Γ,,A||-<l> A' ≅ B']) :
  [Γ,, A |- A⟨@wk1 Γ A⟩ ≅ A'] ->
  [Γ ,, A ||-<l> tRel 0 : A' | RAB].
Proof.
  intros convA.
  eapply Split_return.
  1: now eapply wfc_convty.
  intros Δ wfΔ ρ oRAB.
  assert ([Γ,, A |-[ ta ] tRel 0 : A'])
    by (eapply ty_conv, convA; eapply ty_var0'; gtyping).
  eapply reflectLR.
  + now eapply ty_wk.
  + now eapply ty_wk.
  + now eapply convneu_wk, convneu_var.
Qed.

Lemma var0 {l Γ A A' B'} (RA : [ Γ,,A  ||-<l> A' ≅ B']) :
  A⟨@wk1 Γ A⟩ = A' ->
  [Γ ,, A ||-<l> tRel 0 : A' | RA].
Proof.
  intros <-; eapply var0conv; tea.
  eapply lrefl. now escape.
Qed.

End Neutral.



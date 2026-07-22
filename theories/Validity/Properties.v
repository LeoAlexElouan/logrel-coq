From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.Validity Require Import Validity Irrelevance.
From LogRel.LogicalRelation.Introductions Require Ell.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Properties.
Context `{GenericTypingProperties}.

Lemma wellformedSubstEq {Γ Γ' σ σ' Δ} (VΓ : [||-v Γ ≅ Γ' ]) (wfΔ : [|- Δ]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> [Δ |-s σ ≅ σ' : Γ].
Proof.
  revert Δ wfΔ σ σ'; indValid VΓ.
  - intros. apply conv_sempty.
  - intros * ih ???? []. now eapply conv_sconsε, ih.
  - intros * ih ???? []. apply conv_scons.
    + now eapply ih.
    + now escape.
  - intros * ih ???? []. apply conv_scons.
    + now eapply ih.
    + now escape.
Qed.

Lemma consSubst {Γ Γ' σ σ' t u l A A' Δ} (VΓ : [||-v Γ ≅ Γ']) (wfΔ : [|- Δ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vtu : [Δ ||-<l> t ≅ u : A[σ] | validTyExt VA wfΔ Vσσ']) :
  [Δ ||-v (to_subst (t..)) ∘s (up_subst σ) ≅ (to_subst (u..)) ∘s (up_subst σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; tea.
  + eapply irrelevanceSubstEqExt, Vσσ'; constructor;
    cbn; unfold funcomp; cbn; now bsimpl.
  + eapply (irrLREq (validTyExt VA wfΔ Vσσ')), Vtu.
    eapply subst_subst_eq; constructor; cbn; unfold funcomp; cbn; now bsimpl.
Qed.

Lemma consValidSubst {Γ Γ' σ σ' t u l A A' Δ} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]}
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Δ ||-v σ ∘s (to_subst t..) ≅  σ' ∘s (to_subst u..) : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve opector; intros; tea.
  + now rewrite !tail_single_subst.
  + unshelve eapply irrLREq, validTmExt, Vt; tea.
    now rewrite tail_single_subst.
Qed.



(* Lemma consValidSubst {Γ Γ' σ σ' t u l A A' Δ} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]}
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Δ ||-v (t[σ] .: σ) ≅  (u[σ'] .: σ') : Γ ,, A | validSnoc VΓ VA | wfΔ ].
Proof.
  unshelve econstructor; intros; tea.
  now apply validTmExt.
Qed. *)

Lemma wkSubst {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) :
  forall {σ σ' Δ Δ'}  (wfΔ : [|- Δ]) (wfΔ' : [|- Δ']) (ρ : Δ' ≤ Δ),
  [Δ  ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  [Δ' ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfΔ' ].
Proof.
  indValid VΓ.
  - intros * []. constructor.
  - intros * ih * [htl i hhd hi hin]; unshelve econstructor.
    + eapply ren_index, i; eapply ρ.
    + eapply irrelevanceSubstEqExt, ih with (ρ:=ρ); tea; constructor; cbn; now bsimpl.
    + change (subst_alpha ?σ⟨ρ⟩ 0) with (ρ.(Fwk) (subst_alpha σ 0)). now f_equal.
    + change (subst_alpha ?σ⟨ρ⟩ 0) with (ρ.(Fwk) (subst_alpha σ 0)). rewrite ren_index_to_ren. now f_equal.
    + intros n b hin'. eapply well_Fwk_in, hin, hin'.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply irrelevanceSubstEqExt, ih with (ρ:=ρ) ; tea; constructor; cbn; bsimpl; reflexivity.
    + eapply irrLREq.
      2: now unshelve now eapply wkLR.
      rewrite subst_ren_wk.
      eapply subst_subst_eq; constructor; reflexivity.
  - intros * ih * [tl hd]; unshelve econstructor.
    + eapply irrelevanceSubstEqExt, ih with (ρ:=ρ) ; tea; constructor; cbn; bsimpl; reflexivity.
    + unshelve now eapply irrEll, wkEll.
      change (arr' Δ' tNat tBool) with (arr' Δ tNat tBool)⟨ρ⟩.
      now eapply wkLRTy, (validTyExt VNtoB wfΔ tl).
Qed.

Lemma wk1Subst {Γ Γ' σ σ' Δ F} (VΓ : [||-v Γ ≅ Γ'])
  (wfΔ : [|- Δ]) (wfF : [Δ |- F]) :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] ->
  let ρ := @wk1 Δ F in
  [Δ ,, F ||-v σ ⟨ ρ ⟩ ≅ σ' ⟨ ρ ⟩ : Γ | VΓ | wfc_cons wfΔ wfF ].
Proof.
  intro vσσ'. eapply wkSubst ; eassumption.
Qed.

Lemma consWkSubst {Γ Γ' Δ Ξ A A' σ σ' a b l} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (ρ : Ξ ≤ Δ) wfΞ
  (Rab : [Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | wkLRTy ρ wfΞ (VA.(validTyExt) _ Vσσ')]) :
  [Ξ ||-v (to_subst (a..)) ∘s (up_subst σ⟨ρ⟩) ≅ (to_subst (b..)) ∘s (up_subst σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ ].
Proof.
  unshelve eapply consSubst.
  1: now eapply wkSubst.
  eapply irrLREq; tea; now rewrite subst_ren_wk.
Qed.

Lemma consWkSubstEq {Γ Γ' Δ Ξ A A' B σ σ' a b l} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  (ρ : Ξ ≤ Δ) wfΞ {RA : [Ξ ||-<l> A[σ]⟨ρ⟩ ≅ B]}
  (Rab : [Ξ ||-<l> a ≅ b : A[σ]⟨ρ⟩ | RA]) :
  [Ξ ||-v (to_subst (a..)) ∘s (up_subst σ⟨ρ⟩) ≅ (to_subst (b..)) ∘s (up_subst σ'⟨ρ⟩) : Γ ,, A | validSnoc VΓ VA | wfΞ ].
Proof.
  unshelve eapply consSubst.
  1: now eapply wkSubst.
  eapply irrLREq; tea; now rewrite subst_ren_wk.
Qed.


(* Lemma liftSubst {Γ Γ' σ σ' Δ lF F F'}
  (VΓ : [||-v Γ ≅ Γ']) (wfΔ : [|- Δ])
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let ρ := @wk1 Δ F[σ] in
  let wfΔF := wfc_cons wfΔ (escapeSplit (validTyExt VF wfΔ Vσσ')) in
  [Δ ,, F[σ] ||-v (tRel 0 .: σ ⟨ ρ ⟩) ≅ (tRel 0 .: σ' ⟨ ρ ⟩) : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; unshelve econstructor.
  + now apply wk1Subst.
  + eapply var0; unfold ρ; now bsimpl.
Qed.

Lemma liftSubst' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let wfΔF := wfc_cons wfΔ (escapeSplit (validTyExt VF wfΔ Vσ)) in
  [Δ ,, F[σ] ||-v up_term_term σ ≅ up_term_term σ' : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; eapply irrelevanceSubstEqExt.
  3: unshelve eapply liftSubst.
  1-2: intros ?; now bsimpl.
Qed.

Lemma liftSubstSym' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := symValid (validSnoc VΓ VF) in
  let wfΔF := wfc_cons wfΔ (escapeSplit (validTyExt (symValidTy' VF) wfΔ (symSubst _ _ _ _ Vσ))) in
  [Δ ,, F'[σ'] ||-v up_term_term σ' ≅ up_term_term σ : Γ' ,, F' | VΓF | wfΔF ].
Proof.
  unshelve eapply irrelevanceSubst, liftSubst'; cycle 3; [now eapply symValidTy'|..]; tea.
  now eapply symSubst.
Qed. *)


Lemma wk_up_wk1_subst σ Γ A : σ⟨@wk1 Γ A⟩ =s (@wk1 Γ A >>s up_subst σ).
Proof.
  unfold wk_subst_comp, up_subst. cbn. bsimpl.
  constructor.
  + cbn. bsimpl. intros n. cbn. now bsimpl.
  + cbn. now bsimpl.
Qed.

Lemma liftSubst' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := validSnoc VΓ VF in
  let wfΔF := wfc_cons wfΔ (escapeSplit (validTyExt VF wfΔ Vσ)) in
  [Δ ,, term_decl F[σ] ||-v up_subst σ ≅ up_subst σ' : Γ ,, F | VΓF | wfΔF ].
Proof.
  intros; unshelve opector.
  + eapply irrelevanceSubstEqExt, wk1Subst, Vσ.
    all: now rewrite wk_up_wk1_subst, wk1_tail.
  + cbn -[Wpack].
    eapply var0.
    now rewrite subst_ren_wk, wk_up_wk1_subst, wk1_tail.
Qed.
Lemma liftSubstSym' {Γ Γ' σ σ' Δ lF F F'} {VΓ : [||-v Γ ≅ Γ' ]} {wfΔ : [|- Δ]}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (Vσ : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]) :
  let VΓF := symValid (validSnoc VΓ VF) in
  let wfΔF := wfc_cons wfΔ (escapeSplit (validTyExt (symValidTy' VF) wfΔ (symSubst _ _ _ _ Vσ))) in
  [Δ ,, term_decl F'[σ'] ||-v up_subst σ' ≅ up_subst σ : Γ' ,, F' | VΓF | wfΔF ].
Proof.
  unshelve eapply irrelevanceSubst, liftSubst'; cycle 3; [now eapply symValidTy'|..]; tea.
  now eapply symSubst.
Qed.



Lemma wk1ValidTy {Γ Γ' lA A A' lF F F'} {VΓ : [||-v Γ ≅ Γ']} (VF : [Γ ||-v<lF> F ≅ F' | VΓ]) :
  [Γ ||-v<lA> A ≅ A' | VΓ] ->
  [Γ ,, F ||-v<lA> A ⟨ @wk1 Γ F ⟩ ≅ A' ⟨ @wk1 Γ' F' ⟩ | validSnoc VΓ VF ].
Proof.
  intros VA; constructor; intros * [hd tl].
  rewrite 2 wk1_subst; now eapply validTyExt.
Qed.

Lemma wk1ValidTm {Γ Γ' lA t u A A' lF F F'} {VΓ : [||-v Γ ≅ Γ']}
  (VF : [Γ ||-v<lF> F ≅ F' | VΓ])
  (VA : [Γ ||-v<lA> A ≅ A' | VΓ])
  (Vt : [Γ ||-v<lA> t ≅ u : A | VΓ | VA]) (ρ := @wk1 Γ F):
  [Γ,, F ||-v<lA> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | validSnoc VΓ VF | wk1ValidTy VF VA].
Proof.
  constructor; intros ???? []; rewrite !(wk1_subst t), !wk1_subst.
  now unshelve (eapply irrLREq, validTmExt ; tea; now rewrite wk1_subst).
Qed.

Lemma tail_double_subst σ t u: tail_subst (σ ∘s to_subst (t.: u..))  = σ ∘s to_subst u.. .
Proof. destruct σ as [σ ρ]. reflexivity. Qed.

Lemma cons2ValidSubst {Γ Γ' σ σ' t t' u u' l A A' B B' Δ} {VΓ : [||-v Γ ≅ Γ']} {wfΔ : [|- Δ]}
  (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ])
  {VA : [Γ ||-v<l> A ≅ A' | VΓ]}
  {VB : [Γ ||-v<l> B ≅ B' | VΓ]}
  (Vt : [Γ ||-v<l> t ≅ t' : A | VΓ | VA])
  (Vu : [Γ ||-v<l> u ≅ u' : B | VΓ | VB]) :
  [Δ ||-v σ ∘s to_subst (t.:u..) ≅  σ' ∘s to_subst (t'.: u'..) : Γ ,, B ,, term_decl A⟨@wk1 Γ B⟩  | validSnoc (validSnoc VΓ VB) (wk1ValidTy VB VA) | wfΔ ].
Proof.
  unshelve opector; intros; tea.
  + rewrite !tail_double_subst.
    eapply consValidSubst; tea.
  + unshelve eapply irrLREq, validTmExt, Vt; tea.
    now rewrite tail_double_subst, <- subst_comp_on,
      <- to_subst_sound, shift_subst1.
Qed.

Lemma embValidTy@{u i j k l} {Γ Γ' l l' A A'}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']} (h : l << l')
    (VA : typeValidity@{u i j k l} Γ _ VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ _ VΓ l' A A' (*[Γ ||-v<l'> A |VΓ]*).
Proof.
  constructor; intros ???? RA%(validTyExt VA _).
  eapply Monad.Split_hom_PSh, RA.
  intros Ξ wfΞ ρΞ [pack].
  exists pack; now eapply LR_embedding.
Defined.

Lemma embValidTyOne @{u i j k l} {Γ Γ' l A A'}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']}
    (VA : typeValidity@{u i j k l} Γ Γ' VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)) :
    typeValidity@{u i j k l} Γ Γ' VΓ one A A' (*[Γ ||-v<one> A |VΓ]*).
Proof.
  destruct l; tea; now eapply (embValidTy Oi).
Defined.

Lemma soundCtxId {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) :
  ∑ wfΓ : [|- Γ], [Γ ||-v subst_id : Γ | VΓ | wfΓ].
Proof.
  indValid VΓ.
  - intros; eexists wfc_nil; constructor.
  - intros ?????? VΓ VF [wfΓ ih].
    pose (wfΓF := wfc_consε (F:=F) wfΓ).
(*     pose proof (RA := validTyExt VA _ ih). *)
(*     assert (hA : [Γ |- A]) by (rewrite <- subst_rel; exact (escapeSplit RA)). *)
(*     pose (wfΓA := wfc_cons wfΓ hA). *)
    exists wfΓF.
    unshelve econstructor.
    + eapply index_0.
    + eapply irrelevanceSubstEqExt,
        wkSubst with (ρ:=wk_alphastep F (@wk_id Γ)), ih;
        constructor; cbn; bsimpl; reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply Fwk_id.
  - intros ????? VΓ VA [wfΓ ih].
    pose proof (RA := validTyExt VA _ ih).
    assert (hA : [Γ |- A]) by (rewrite subst_id_on; exact (escapeSplit RA)).
    pose (wfΓA := wfc_cons wfΓ hA).
    assert (Vs : [VΓ | _ ||-v tail_subst subst_id : _ | wfΓA]).
    { eapply irrelevanceSubstEqExt, wkSubst with (ρ := @wk1 Γ A), ih;
        constructor; cbn; bsimpl; try reflexivity; eapply term_decl; tea.
    }
    exists wfΓA; exists Vs.
    eapply var0; tea.
    now rewrite <- wk1_subst with (A:= A) (Γ:=Γ), <- subst_id_on.
  - intros ???? VΓ VNtoB [wfΓ ih].
    pose (wfΓℓ := wfc_consell wfΓ : [|-Γ,,ℓ]).
    assert (Vs : [VΓ | _ ||-v tail_subst subst_id : _ | wfΓℓ]).
    { eapply irrelevanceSubstEqExt, wkSubst with (ρ := @wk1 Γ ℓ), ih;
        constructor; cbn; bsimpl; try reflexivity; eapply ell_decl; tea. }
    exists wfΓℓ; exists Vs.
    eapply Ell.var0Ell.
Qed.


Definition escapeValid {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) : [|-Γ] := (soundCtxId VΓ).π1.

Definition idSubst {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v subst_id : Γ | VΓ | _] := (soundCtxId VΓ).π2.

Lemma redValidTy {Γ Γ' A A' l} {VΓ : [||-v Γ ≅ Γ']} (vA : [_ ||-v<l> A ≅ A' | VΓ ]) : [Γ ||-<l> A ≅ A'].
Proof. intros; instValid (idSubst VΓ); now rewrite <- !subst_id_on in *. Qed.

Lemma redValidTm {Γ Γ' A A' l t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ ]}
  (Vt : [Γ ||-v<l> t ≅ t' : _ | _ | VA]) :  [Γ ||-<l> t ≅ t' : _ | redValidTy VA ].
Proof.
  intros; instValid (idSubst VΓ); rewrite <- !subst_id_on, <- !(subst_id_on t) in *; eapply irrLREq; tea;
  now rewrite subst_id_on.
Qed.

Lemma redValidTm' {Γ Γ' A A' l t t'} {VΓ : [||-v Γ ≅ Γ']} {VA : [_ ||-v<l> A ≅ A' | VΓ ]}
  (RA : [Γ ||-<l> A ≅ A']) (Vt : [Γ ||-v<l> t ≅ t' : _ | _ | VA]) :  [Γ ||-<l> t ≅ t' : _ | RA].
Proof. now eapply irrLR, redValidTm. Qed.


Lemma wkrenSubst {Γ Δ} (ρ : Δ ≤ Γ) :
  forall {Γ' Δ'} (VΓ : [||-v Γ ≅ Γ']) (VΔ : [||-v Δ ≅ Δ'])  {Ξ σ σ'} (wfΞ : [|- Ξ]),
  [VΔ | Ξ ||-v σ ≅ σ' : _ | wfΞ] -> [VΓ | Ξ ||-v ρ >>s σ ≅ ρ >>s σ' : _ | wfΞ].
Proof.
  induction ρ using wk_induction; [|destruct A as [A | ℓ]..| | ]; intros * Vσ.
  + pose proof (invValidity VΓ) as (e&h); subst; cbn in h; subst.
    constructor.
  + pose proof (invValidity VΔ) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [htl hhd].
    eapply (IHρ _ _ _ _ _ _ _ _ htl).
  + pose proof (invValidity VΔ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [htl hhd].
    eapply (IHρ _ _ _ _ _ _ _ _ htl).
  + change (term_decl A)⟨ρ⟩ with (term_decl A⟨ρ⟩) in VΔ.
    pose proof (invValidity VΔ) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    pose proof (invValidity VΓ) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [tl hd]. opector.
    - refine (IHρ _ _ _ _ _ _ _ _ tl).
    - eapply irrLREqCum; tea.
      now rewrite wk_subst_comp_on.
  + pose proof (invValidity VΔ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    pose proof (invValidity VΓ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [tl hd]. opector.
    - refine (IHρ _ _ _ _ _ _ _ _ tl).
    - eapply irrEll; tea.
  + pose proof (invValidity VΔ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [htl i hd hi hin].
    eapply (IHρ _ _ _ _ _ _ _ _ htl).
  + pose proof (invValidity VΔ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    pose proof (invValidity VΓ) as (?&?&?&?&e&h); subst; cbn in h; subst.
    destruct Vσ as [htl i hd hi hin].
    econstructor; tea.
    - refine (IHρ _ _ _ _ _ _ _ _ htl).
    - now eapply Fwk_compose.
Qed.

Lemma wkValidTy {l Γ Γ' Δ Δ' A A'} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ ≅ Γ'])
  (VΔ : [||-v Δ ≅ Δ'])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ]) :
  [Δ ||-v<l> A⟨ρ⟩ ≅ A'⟨ρ⟩ | VΔ].
Proof.
  constructor; intros; cbn; rewrite !wk_subst_comp_on.
  eapply validTyExt; tea; now eapply wkrenSubst.
Qed.

Lemma wkValidTm {l Γ Γ' Δ Δ' A A' t u} (ρ : Δ ≤ Γ)
  (VΓ : [||-v Γ ≅ Γ'])
  (VΔ : [||-v Δ ≅ Δ'])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vt : [Γ ||-v<l> t ≅ u: A | VΓ | VA]) :
  [Δ ||-v<l> t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩ | VΔ | wkValidTy ρ VΓ VΔ VA].
Proof.
  econstructor; intros; rewrite !wk_subst_comp_on, !wk_subst_comp_on with (t:=t).
  (unshelve now eapply irrLREq, validTmExt; tea; rewrite wk_subst_comp_on); tea.
  now eapply wkrenSubst.
Qed.

Lemma escapeValidTy {Γ Γ' A A' l} (VΓ : [||-v Γ ≅ Γ']) : [_ ||-v<l> A ≅ A' | VΓ ] -> [Γ |- A] × [Γ |- A'] × [Γ |-  A ≅ A'].
Proof.
  intros VA;  generalize (validTyExt VA _ (idSubst VΓ)); rewrite <- 2!subst_id_on; intros; now escape.
Qed.

Lemma escapeValidTm {Γ Γ' A A' l t t'} (VΓ : [||-v Γ ≅ Γ'])
  (VA : [_ ||-v<l> A ≅ A' | VΓ ]) :
  [_ ||-v<l> t ≅ t' : _ | _ | VA] -> [Γ |- t : A] × [Γ |- t' : A] × [Γ |- t ≅ t' : A].
Proof.
  intros Vt; pose proof (validTmExt Vt _ (idSubst VΓ)); escape.
  rewrite <- !subst_id_on in *. now repeat split.
Qed.

Lemma redSubstValid {Γ Γ' A A' t u l}
  (VΓ : [||-v Γ ≅ Γ'])
  (red : [Γ ||-v t ⤳* u : A | VΓ])
  (VA : [Γ ||-v<l> A ≅ A' | VΓ])
  (Vu : [Γ ||-v<l> u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : A | VΓ | VA].
Proof.
  constructor; intros. eapply redSubstLeftTmEq.
  1: now eapply validTmExt.
  now eapply validRed.
Qed.

Lemma SsubstS {Γ Γ' F F' G G' t t' l} {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VG : [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ VF])
  (Vt : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ].
Proof.
  constructor; intros. rewrite 2to_subst_sound, 2subst_comp_on.
  eapply validTyExt; tea; now eapply consValidSubst.
Qed.

Lemma substS {Γ Γ' F F' G G' t t' l} {VΓ : [||-v Γ ≅ Γ']}
  {VF : [Γ ||-v<l> F ≅ F' | VΓ]}
  (VG : [Γ,, F ||-v<l> G ≅ G' | validSnoc VΓ VF])
  (Vt : [Γ ||-v<l> t ≅ t' : F | VΓ | VF]) :
  [Γ ||-v<l> G[t..] ≅ G'[t'..] | VΓ].
Proof.
  constructor; intros. rewrite 2to_subst_sound, 2subst_comp_on.
  eapply validTyExt; tea; now eapply consValidSubst.
Qed.

Lemma substSTm {Γ Γ' F F' G G' t t' f f' l} (VΓ : [||-v Γ ≅ Γ'])
  (VF : [Γ ||-v<l> F ≅ F' | VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ ,, F ||-v<l> G ≅ G' | VΓF])
  (Vtt' : [Γ ||-v<l> t ≅ t' : F | VΓ | VF])
  (Vff' : [Γ ,, F ||-v<l> f ≅ f' : G | VΓF | VG]) :
  [Γ ||-v<l> f[t..] ≅ f'[t'..] : G[t..] | VΓ | substS VG Vtt'].
Proof.
  constructor; intros.
  replace f[t..][σ] with f[σ ∘s to_subst t..].
  replace f'[t'..][σ'] with f'[σ' ∘s to_subst t'..].
  2,3: now rewrite to_subst_sound, subst_comp_on.
  eapply irrLREq.
  1: symmetry; now rewrite to_subst_sound, subst_comp_on.
  (unshelve now eapply validTmExt); tea.
  now eapply consValidSubst.
Qed.

(* Lemma substLiftS {Γ Γ' F F' G G' t t' l} (VΓ : [||-v Γ ≅ Γ'])
  (VF : [Γ ||-v<l> F ≅ F'| VΓ])
  (VΓF := validSnoc VΓ VF)
  (VG : [Γ,, F ||-v<l> G ≅ G' | VΓF])
  (VF' := wk1ValidTy VF VF)
  (Vt : [Γ,, F ||-v<l> t ≅ t' : F⟨@wk1 Γ F⟩ | VΓF | VF']) :
  [Γ ,, F ||-v<l> G[t]⇑ ≅ G'[t']⇑ | VΓF].
Proof.
  constructor; intros; erewrite 2! liftSubstComm.
  eapply validTyExt; tea; opector.
  1: now eapply wkrenSubst.
  now unshelve now eapply irrLREq, validTmExt; tea; rewrite ren_subst.
Qed. *)

Lemma substLiftS {Γ Γ' F F' G G' A A' t t' l} (VΓ : [||-v Γ ≅ Γ'])
  (VF : [Γ ||-v<l> F ≅ F'| VΓ])
  (VΓF := validSnoc VΓ VF)
  (VA : [Γ ||-v<l> A ≅ A'| VΓ])
  (VΓA := validSnoc VΓ VA)
  (VG : [Γ,, A ||-v<l> G ≅ G' | VΓA])
  (VA' := wk1ValidTy VF VA)
  (Vt : [Γ,, F ||-v<l> t ≅ t' : A⟨@wk1 Γ F⟩ | VΓF | VA']) :
  [Γ ,, F ||-v<l> G⟨wk_up A (@wk1 Γ F)⟩[t..] ≅ G'⟨wk_up A' (@wk1 Γ F)⟩[t'..] | VΓF].
Proof.
  constructor; intros.
  rewrite 2!to_subst_sound, 2subst_comp_on, 2wk_subst_comp_on.
  eapply validTyExt; tea. opector.
  1: now eapply wkrenSubst.
  now unshelve now eapply irrLREq, validTmExt; tea; rewrite wk_subst_comp_on.
Qed.


End Properties.

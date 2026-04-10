From Stdlib Require Import ssrbool CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Id.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Poly Var ValidityTactics.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Set Universe Polymorphism.

Section Id.
Context `{GenericTypingProperties}.

  Lemma IdValid {Γ Γ' l A A' x x' y y'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ].
  Proof.
    constructor; intros; instValid vσσ'; now eapply IdRed.
  Qed.

  Lemma IdValidU {Γ Γ' l A A' x x' y y'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VU := UValid VΓ)
    (VAU : [_ ||-v<one> A ≅ A' : U | VΓ | VU])
    (VA := univValid l VAU)
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA]) :
    [_ ||-v<one> tId A x y ≅ tId A' x' y' : _ | VΓ | VU].
  Proof.
    constructor; intros; instValid Vσσ'.
    unshelve eapply IdCongRedU; refold; tea.
    1,2: now eapply irrLR.
  Qed.

  Lemma reflValid {Γ Γ' l A A' B x x'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VId : [_ ||-v<l> tId A x x ≅ B | VΓ]) :
    [_ ||-v<l> tRefl A x ≅ tRefl A' x' : _ | _ | VId].
  Proof.
    constructor; intros; instValid Vσσ'; escape.
    eapply reflCongRed0; tea.
  Qed.


  Lemma subst_scons2 (P e y : term) (σ : nat -> term) : P[e .: y..][σ] = P [e[σ] .: (y[σ] .: σ)].
  Proof. now asimpl. Qed.

  Lemma subst_upup_scons2 (P e y : term) (σ : nat -> term) : P[up_term_term (up_term_term σ)][e .: y..] = P [e .: (y .: σ)].
  Proof. now asimpl. Qed.


  Lemma idElimMotiveCtxIdValid {Γ Γ' l A A' x x'}
    (VΓ : [||-v Γ ≅ Γ' ])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    [Γ,, A ||-v< l > tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) ≅ tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0) | validSnoc VΓ VA].
  Proof.
    unshelve eapply IdValid.
    3: eapply var0Valid.
    erewrite wk1_irr; now eapply wk1ValidTm.
  Qed.


  Definition idElimMotiveCtxEqStmt Γ Γ' A A' x x' :=
    [||-v (Γ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) ≅ (Γ',, A' ,, tId A'⟨@wk1 Γ' A'⟩ x'⟨@wk1 Γ' A'⟩ (tRel 0))].

  Lemma idElimMotiveCtxEq {Γ Γ' l A A' x x'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vxx' : [_ ||-v<l> x ≅ x' : _ | _ | VA]) :
    idElimMotiveCtxEqStmt Γ Γ' A A' x x'.
  Proof.
    now eapply validSnoc, idElimMotiveCtxIdValid.
  Defined.


  Lemma idElimMotiveScons2Valid {Γ Γ' l A A' x x' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VΓext := idElimMotiveCtxEq VΓ VA Vx : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    Δ (wfΔ: [ |-[ ta ] Δ]) {σ σ'} (Vσσ': [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ]) :
      [VΓext | Δ ||-v σ ∘s to_subst (e.: y..) ≅ σ' ∘s to_subst (e' .: y'..) : _ | wfΔ].
  Proof.
    opector.
    + rewrite tail_double_subst.
      eapply consValidSubst; tea.
    + revert e0; rewrite tail_double_subst; intros htl.
      unshelve eapply irrLREq, validTmExt, Ve; tea.
      change (tId ?A ?x ?y)[?σ] with (tId A[σ] x[σ] y[σ]).
      now rewrite <- !subst_comp_on, <- !to_subst_sound, !shift_subst1.
  Qed.

  Lemma substIdElimMotive {Γ Γ' l A A' x x' P P' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (Vy : [Γ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId]) :
    [_ ||-v<l> P[e .: y ..] ≅ P'[e' .: y' ..] | VΓ].
  Proof.
    constructor; intros.
    rewrite 2to_subst_sound, 2subst_comp_on.
    unshelve (eapply validTyExt; tea); tea.
    now unshelve now eapply irrelevanceSubst, idElimMotiveScons2Valid.
  Qed.

  Lemma up_twice_subst t a b σ :
    t[up_subst (up_subst σ)][a[σ] .: b[σ]..] =
    t[a .: b..][σ].
  Proof. now bsimpl. Qed.

  Lemma idElimMotive_Idsubst_eq {Γ Δ A x σ} :
    tId A[σ]⟨@wk1 Δ A[σ]⟩ x[σ]⟨@wk1 Δ A[σ]⟩ (tRel 0) =
      (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0))[up_subst σ].
  Proof. change (tId ?A ?x ?y)[?σ] with (tId A[σ] x[σ] y[σ]); f_equal; eapply subst_up_wk1. Qed.

  Lemma idElimMotiveScons2Red {Γ Γ' l A A' x x' y y' e e'}
    {VΓ : [||-v Γ ≅ Γ']}
    {VA : [_ ||-v<l> A ≅ A' | VΓ]}
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    {Δ} {wfΔ : [|-Δ]}
    {σ σ'} (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓ | wfΔ])
    {RVA : [Δ ||-<l> A[σ] ≅ A'[σ']]}
    (Ry : [ RVA |  _ ||- y ≅ y' : _])
    {RId : [Δ ||-<l> tId A[σ] x[σ] y ≅ tId A'[σ'] x'[σ'] y']}
    (Re : [RId | _ ||- e ≅ e' : _]) :
      [VΓext | Δ ||-v to_subst (e .: y ..) ∘s up_subst (up_subst σ) ≅ to_subst (e' .: y' ..) ∘s up_subst (up_subst σ') : _ | wfΔ].
  Proof.
    pose proof (invValiditySnoc VΓext) as (?&VΓA& VIdA &->).
    pose proof (invValiditySnoc VΓA) as (?&?& ? &->).
    eapply irrelevanceSubstEqExt,
      (consSubst (t:=e) (u:=e') (σ:= to_subst y.. ∘s (up_subst σ)) (σ':= to_subst y'.. ∘s (up_subst σ'))).
    { destruct σ as [σ ρ]. constructor; try reflexivity. intros [| []]. cbn. reflexivity. cbn. now bsimpl. cbn. now bsimpl. }
    { destruct σ as [σ ρ]. constructor; try reflexivity. intros [| []]. cbn. reflexivity. cbn. now bsimpl. cbn. now bsimpl. }
    eapply irrLREqCum, Re.
    change (tId ?A ?x ?y)[?σ] with (tId A[σ] x[σ] y[σ]).
    now erewrite <- !subst_comp_on, <-!to_subst_sound, <- !subst_up_wk1, !shift_subst1.
    Unshelve.
    { eapply consSubst, irrLREqCum, Ry. reflexivity. }
    all: tea.
    Unshelve. now eapply irrelevanceSubst.
  Qed.

  Lemma IdElimValid {Γ Γ' l A A' x x' P P' hr hr' y y' e e'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VA : [_ ||-v<l> A ≅ A' | VΓ ])
    (Vx : [_ ||-v<l> x ≅ x' : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A A' x x')
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (VIdxx := (IdValid VΓ VA Vx Vx))
    (VPhr := substIdElimMotive VΓ VA Vx VΓext VP Vx VIdxx (reflValid VΓ VA Vx _))
    (Vhr : [_ ||-v<l> hr ≅ hr' : _ | _ | VPhr ])
    (Vy : [_ ||-v<l> y ≅ y' : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId A' x' y' | VΓ])
    (Ve : [_ ||-v<l> e ≅ e' : _ | _ | VId])
    (VPye := substIdElimMotive VΓ VA Vx VΓext VP Vy VId Ve) :
    [_ ||-v<l> tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : _ | _ | VPye].
  Proof.
    constructor; intros.
    instValid Vσσ'.
    pose proof (Vuu0 := liftSubst' (idElimMotiveCtxIdValid VΓ VA Vx) (liftSubst' VA Vσσ')).
    set (wfΔ' := wfc_cons _ _) in Vuu0.
    epose proof (Vuu := irrelevanceSubst _ VΓext _ wfΔ' Vuu0).
    instValid Vuu.
    eapply irrLREq; [now rewrite <- up_twice_subst|].
    change (tIdElim ?A ?x ?P ?hr ?y ?e)[?σ] with (tIdElim A[σ] x[σ] P[up_subst (up_subst σ)] hr[σ] y[σ] e[σ]).
    (unshelve (eapply idElimCongRed; tea)); tea.
    - intros ???? Ry Re.
      epose proof (Vext := idElimMotiveScons2Red Vx VΓext Vσσ' Ry Re).
      instValid Vext; now rewrite 2to_subst_sound, 2subst_comp_on.
    - eapply irrLR, RVe.
    - erewrite idElimMotive_Idsubst_eq; now eapply escapeSplit.
    - erewrite idElimMotive_Idsubst_eq.
      pose (t := idElimMotiveCtxIdValid _ (symValidTy' VA) (symValidTm' Vx)).
      pose proof (Vuu1 := liftSubst' t (liftSubst' (symValidTy' VA) (symSubst _ _ _ wfΔ Vσσ'))).
      set (wfΔ'' := wfc_cons _ _) in Vuu1.
      now unshelve eapply (escapeSplit (validTyExt (symValidTy' VP) _ (irrelevanceSubst _ _ _ _ Vuu1))).
    - erewrite idElimMotive_Idsubst_eq; now eapply escapeSplitTy.
    - intros Ξ wfΞ ρΞ z z' f f' ? Rz Rf.
      replace P[_]⟨_⟩ with P[up_subst (up_subst σ⟨ρΞ⟩)]
        by now rewrite subst_ren_wk, 2eq_upwk.
      replace P'[_]⟨_⟩ with P'[up_subst (up_subst σ'⟨ρΞ⟩)]
        by now rewrite subst_ren_wk, 2eq_upwk.
      rewrite !to_subst_sound, !subst_comp_on.
      eapply validTyExt; tea.
      unshelve eapply wkSubst in Vσσ' as VρΞ; tea.
      eapply idElimMotiveScons2Red.
      + eapply Vx.
      + eapply VρΞ.
      + eapply irrLREq, Rz.
        eapply subst_ren_wk.
      + eapply irrLREq, Rf.
        now rewrite 2 subst_ren_wk.
    - eapply irrLREq; tea; clear; now bsimpl.
    Unshelve.
    + now rewrite <- 2 subst_ren_wk.
    + rewrite <- 4 subst_ren_wk.
      eapply (IdRed RAρ (wkLRTm ρΞ wfΞ RVx) Rz).
  Qed.

  Lemma subst_subst_twice t a b σ :
    t[a .: b..][σ] = t[a[σ] .: (b[σ] .: σ)].
  Proof. now bsimpl. Qed.

  Lemma subst_refl A x σ : (tRefl A x)[σ] = tRefl A[σ] x[σ].
  Proof. reflexivity. Qed.

  Lemma IdElimReflValid {Γ Γ' l A x P  P' hr y B z}
    (VΓ : [||-v Γ ≅ Γ' ])
    (VA : [_ ||-v<l> A ≅ B | VΓ])
    (Vxy : [_ ||-v<l> x ≅ y : _ | _ | VA])
    (VΓext : idElimMotiveCtxEqStmt Γ Γ' A B x y)
    (VP : [_ ||-v<l> P ≅ P' | VΓext])
    (VIdxx := (IdValid VΓ VA Vxy Vxy))
    (Vrflx := reflValid VΓ VA Vxy _)
    (VPhr := substIdElimMotive VΓ VA Vxy VΓext VP Vxy VIdxx Vrflx)
    (Vhr : [_ ||-v<l> hr : _ | _ | VPhr ])
    (Vxz : [_ ||-v<l> x ≅ z : _ | _ | VA])
    (VId : [Γ ||-v<l> tId A x y ≅ tId B y y | VΓ])
    (VRefl : [_ ||-v<l> tRefl B z : _ | _ | VId])
    (Vyy := urefl Vxy)
    (VPye := substIdElimMotive VΓ VA Vxy VΓext VP Vyy VId VRefl) :
    [_ ||-v<l> tIdElim A x P hr y (tRefl B z) ≅ hr : _ | _ | VPye].
  Proof.
    eapply redSubstValid.
    + constructor; intros; rewrite <-up_twice_subst.
      pose proof (Vuu0 := liftSubst' (idElimMotiveCtxIdValid VΓ VA Vxy) (liftSubst' VA Vσσ')).
      set (wfΔ' := wfc_cons _ _) in Vuu0.
      epose proof (Vuu := irrelevanceSubst _ VΓext _ wfΔ' Vuu0).
      instValid (lrefl Vσσ') ; instValid Vuu ; escape.
      change (tIdElim ?A ?x ?P ?hr ?y ?e)[?σ] with (tIdElim A[σ] x[σ] P[up_subst (up_subst σ)] hr[σ] y[σ] e[σ]).
      change (tRefl ?B ?z)[?σ] with (tRefl B[σ] z[σ]).
      eapply redtm_idElimRefl; tea.
      - now erewrite idElimMotive_Idsubst_eq.
      - now rewrite <-subst_refl, up_twice_subst.
    + unfold idElimMotiveCtxEqStmt in *. (* TODO: there should be something cleaner here !!! *)
      unshelve (eapply irrValidTm; [|tea]); tea.
      1: now eapply lrefl.
      eapply substIdElimMotive.
      2: eapply lrefl, irrValidTy; tea; now eapply lrefl.
      1,2: irrValid.
      eapply reflValid; irrValid.
      Unshelve. 1,3,4: irrValid.
      unfold idElimMotiveCtxEqStmt; irrValid.
  Qed.

End Id.





From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties Introductions.Ell.
From LogRel.Validity Require Import Validity Irrelevance Properties ValidityTactics.
From LogRel.Validity.Introductions Require Import Bool Nat Tree Id SimpleArr.


Section Ell.
  Context `{GenericTypingProperties}.


  Lemma NtoBValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v< l > arr' Γ tNat tBool ≅ arr' Γ tNat tBool | VΓ ].
  Proof.
    eapply simpleArr'Valid.
    + eapply natValid.
    + eapply boolValid.
  Qed.

  Lemma ellValid {Γ Γ' l ℓ} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-vEll< l > ℓ ≅ ℓ | VΓ].
  Proof. constructor; intros. now eapply EllRed. Qed.

  Lemma var0EllValid' {Γ Γ' l} {ℓ ℓ' : ell} (VΓ : [||-v Γ,,ℓ ≅ Γ']) (Vℓ : [Γ,,ℓ ||-vEll<l> ℓ ≅ ℓ' | VΓ]) :
    [Γ,, ℓ ||-vEll<l> tRel 0 : ℓ | VΓ | Vℓ ].
  Proof.
    pose proof (invValidity VΓ) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    constructor; intros.
    eapply irrEll, Vσσ'.
  Qed.

  Lemma in_ctx_ellValid {Γ : context} {ℓ : ell} {n} (inℓ : in_ctx Γ n ℓ)
    : forall {Γ'} (VΓ : [||-v Γ ≅ Γ']), ∑ l ℓ', [Γ ||-vEll<l> ℓ ≅ ℓ' | VΓ].
  Proof.
    pattern Γ, n, ℓ, inℓ.
    eapply ell_in_ctx_induction; clear Γ ℓ n inℓ; intros.
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&Vℓ &e&?); subst; cbn in *; subst.
      do 2 eexists; now eapply (wkValidEll (wk1 ℓ)).
    + destruct A' as [A' | ℓ'].
      - pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA' &e&?); subst; cbn in *; subst.
        destruct (ihinℓ _ VΓ') as (?&?&?).
        do 2 eexists; now eapply (wkValidEll (wk1 A')).
      - pose proof (invValidity VΓ) as (?&?&?&VΓ'&Vℓ &e&?); subst; cbn in *; subst.
        destruct (ihinℓ _ VΓ') as (?&?&?).
        do 2 eexists; now eapply (wkValidEll (wk1 ℓ')).
  Qed.

  Lemma varnEllValid {Γ Γ' l} {ℓ ℓ' : ell} {v} (inℓ : in_ctx Γ v ℓ) (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ : [Γ ||-vEll< l > ℓ ≅ ℓ' | VΓ]) :
    [Γ ||-vEll< l > tRel v ≅ tRel v : _ | VΓ | Vℓ].
  Proof. revert  Γ' VΓ l ℓ' Vℓ.
    pattern Γ, v, ℓ, inℓ.
    eapply ell_in_ctx_induction; clear Γ ℓ v inℓ; intros.
    1: eapply var0EllValid'.
    replace (tRel (shift v)) with (tRel v)⟨@wk1 Γ A'⟩
       by now rewrite wk1_ren_on.
    destruct A' as [A'| ℓ''].
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA'&?&h); subst; cbn in h.
      destruct (in_ctx_ellValid inℓ VΓ') as (?&?&h').
      unshelve eapply irrValidEllTmRfl, wkValidEllTm, ihinℓ.
      7: eapply h'.
      2: eapply VΓ.
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&Vℓ'&?&h); subst; cbn in h.
      destruct (in_ctx_ellValid inℓ VΓ') as (?&?&h').
      unshelve eapply irrValidEllTmRfl, wkValidEllTm, ihinℓ.
      7: eapply h'.
      2: eapply VΓ.
  Qed.

  Lemma evalValid {Γ Γ' l ℓ ℓ' t t'} (VΓ : [||-v Γ ≅ Γ']) (Vℓ : [Γ ||-vEll< l > ℓ ≅ ℓ' | VΓ]) :
    [Γ ||-vEll< l> t ≅ t' : ℓ | VΓ | Vℓ] ->
    [Γ ||-v< l > tEval ℓ t ≅ tEval ℓ t' : arr' Γ tNat tBool | VΓ | NtoBValid VΓ].
  Proof.
    intros Vt; econstructor; intros.
    rewrite <-! subst_eval.
    now unshelve eapply irrLR, evalRedEq, irrEll, Vt.
  Qed.

  Lemma boxValid {Γ Γ' l t t'} {ℓ : ell} (VΓ: [||-v Γ ≅ Γ'])
    (VNtoB : [Γ ||-v< l > arr' Γ tNat tBool | VΓ]) (VB : [Γ ||-v< l > tBool | VΓ]) :
    [Γ ||-v< l> t ≅ t' : _ | VΓ | VNtoB] ->
    (forall n b, in_ell ℓ n b ->
      [Γ ||-v< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | _ | VB]) ->
    [Γ ||-vEll< l > tBox ℓ t ≅ tBox ℓ t' : ℓ | VΓ | ellValid VΓ].
  Proof.
    intros Vtt' Vtnb; econstructor; intros.
    rewrite <-! subst_box.
    unshelve eapply irrEll, boxRed; tea.
    + now unshelve eapply irrLR, Vtt'.
    + intros ?? inn. erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
      now unshelve eapply irrLR, Vtnb.
  Qed.


  Lemma evalnat_to_termValid {Γ Γ' l n k b} {ℓ : ell} (VΓ: [||-v Γ ≅ Γ']) : in_ell ℓ k b ->
    [Γ ||-vEll< l > n : ℓ | _ | ellValid VΓ ] ->
    [Γ ||-v< l > tApp (tEval ℓ n) (nat_to_term k) ≅ bool_to_term b : _ | _ | boolValid VΓ].
  Proof.
    intros inb Vn; constructor; intros.
    rewrite <- subst_app, <- subst_eval, subst_nat_to_term, subst_bool_to_term.
    unshelve eapply irrLR, evalnat_to_termRed; tea.
    unshelve eapply irrEll, Vn; tea.
    now eapply lrefl.
  Qed.

  Lemma etaEllValid {Γ Γ' l} {ℓ: ell} {t} (VΓ : [||-v Γ ≅ Γ' ]) :
    [Γ ||-vEll< l > t : ℓ | _ | ellValid VΓ] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓ t) ≅ t : ℓ | _ | ellValid VΓ].
  Proof.
    intros Vt.
    constructor; intros.
    rewrite <- subst_box, <- subst_eval.
    etransitivity.
    + unshelve eapply irrEll, etaEllRed, irrEll, Vt; tea.
      now eapply lrefl.
    + now unshelve eapply irrEll, Vt.
  Qed.

  Lemma evalRelValid {Γ Γ' l v k b} {ℓ : ell} (VΓ: [||-v Γ ≅ Γ']) : in_ell ℓ k b -> in_ctx Γ v ℓ ->
    [Γ ||-v< l > tApp (tEval ℓ (tRel v)) (nat_to_term k) ≅ bool_to_term b : _ | _ | boolValid VΓ].
  Proof.
    intros inb inℓ.
    now eapply evalnat_to_termValid, varnEllValid.
  Qed.

  Lemma evalBoxValid {Γ Γ' l t} {ℓ : ell} (VΓ: [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > t : _ | _ | NtoBValid VΓ] ->
    (forall k b, in_ell ℓ k b ->
      [Γ ||-v< l > tApp t (nat_to_term k) ≅ bool_to_term b : _ | _ | boolValid VΓ]) ->
    [Γ ||-v< l > tEval ℓ (tBox ℓ t) ≅ t : _ | _ | NtoBValid VΓ].
  Proof.
    intros Vt Vtkb.
    eapply redSubstValid; tea.
    econstructor; intros.
    rewrite <- subst_eval, <- subst_box.
    eapply redtm_evalBox.
    + now instValid Vσσ'; escape.
    + intros n b inb. specialize (Vtkb _ _ inb).
      erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
      now instValid Vσσ'; escape.
  Qed.



Section ellElimValid.
  Context {Γ Γ' l ℓ k}
    (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ)
    (VB := boolValid (l:=l) VΓ)
    (VN := natValid (l:=l) VΓ)
    (VNtoB := NtoBValid (l:=l) VΓ)
    (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false)
    (Vℓt := ellValid (l:=l) (ℓ:=ℓt) VΓ) (Vℓf := ellValid (l:=l) (ℓ:=ℓf) VΓ)
    (VΓt := validSnocℓ VΓ Vℓt) (VΓf := validSnocℓ VΓ Vℓf).

  Let boxEvalℓtValid : [Γ,, ℓt ||-vEll< l > tBox ℓ (tEval ℓt (tRel 0)) : ℓ | VΓt | ellValid _].
  Proof.
    eapply boxValid.
    + unshelve eapply evalValid, var0EllValid'.
      2: eapply ellValid.
    + intros n b inb.
      eapply evalnat_to_termValid.
      - now eapply in_cons_ell; right.
      - eapply var0EllValid'.
  Qed.

  Let boxEvalℓfValid : [Γ,, ℓf ||-vEll< l > tBox ℓ (tEval ℓf (tRel 0)) : ℓ | VΓf | ellValid _].
  Proof.
    eapply boxValid.
    + unshelve eapply evalValid, var0EllValid'.
      2: eapply ellValid.
    + intros n b inb.
      eapply evalnat_to_termValid.
      - now eapply in_cons_ell; right.
      - eapply var0EllValid'.
  Qed.
Generalizable All Variables.
  Lemma up_subst_comp {σ τ} : up_subst (σ ∘s τ) =s (up_subst σ ∘s up_subst τ).
  Proof.
    constructor.
    + intros [].
      { reflexivity. }
      cbn; now bsimpl.
    + reflexivity.
  Qed.
  Lemma up_subst_id : up_subst subst_id =s subst_id.
  Proof.
    repeat constructor.
    intros []; reflexivity.
  Qed.
  Lemma wk_up_subst σ A `(ρ : Ξ ≤ Δ) : up_subst σ ∘r wk_up A ρ =s up_subst (σ ∘r ρ).
  Proof.
    constructor.
    + intros []; reflexivity.
    + reflexivity.
  Qed.
  Lemma tail_scons {t} : tail_subst (to_subst t..) =s subst_id.
  Proof.
    constructor.
    + cbn. now bsimpl.
    + reflexivity.
  Qed.
  Lemma ellElimValid {P P' ht ht' hf hf' t t' b b'} (VP : [Γ,, ℓ ||-v< l > P ≅ P' | validSnocℓ VΓ Vℓ])
    (Vt : [Γ ||-vEll< l > t ≅ t' : _ | _ | Vℓ ]) :
    [Γ,, ℓt ||-v< l > ht ≅ ht' : P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..]
      | VΓt | substEllS (wkValidTy _ _ _ VP) boxEvalℓtValid ] ->
    [Γ,, ℓf ||-v< l > hf ≅ hf' : P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]
      | VΓf | substEllS (wkValidTy _ _ _ VP) boxEvalℓfValid ] ->
    [Γ ||-v< l > b ≅ b' : _ | _ | VB] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ b : _ | _ | VB] ->
    [Γ ||-v< l > tEllElim k ℓ P ht hf t b ≅ tEllElim k ℓ P' ht' hf' t' b' : P[t..] | VΓ | substEllS VP Vt ].
  Proof.
    intros Vht Vhf Vb Vtkb; econstructor; intros.
    rewrite <-2 subst_ellElim.
    assert (Hsubst : forall (t u : term) σ `(ρ : Ξ' ≤ Ξ) d, t[up_subst σ]⟨wk_up d ρ⟩[u..] = t[to_subst u.. ∘s up_subst σ⟨ρ⟩]) by
      now intros; rewrite subst_ren_wk, to_subst_sound, subst_comp_on, eq_upwk.
    unshelve eapply irrLREq, EllElimRedEq; tea.
    + intros Ξ ρΞ wfΞ u u' Ru.
      rewrite ! Hsubst.
      unshelve eapply VP; tea. unshelve eapply consEllSubst, irrEll, Ru.
      now eapply wkSubst.
    + now unshelve eapply irrEll, Vt.
    + symmetry; eapply subst_ren_subst_up.
    + intros Ξ ρΞ wfΞ u u' Ru.
      eapply irrLREq; [shelve|].
      rewrite ! Hsubst.
      unshelve eapply Vht; tea.
      unshelve eapply consEllSubst, irrEll, Ru.
      now eapply wkSubst.
      Unshelve. fold ℓt. rewrite subst_ren_subst_up. f_equal.
      rewrite up_subst_comp.
      now unshelve erewrite <- subst_comp_on, <- up_subst_wk_up_wk1, wk_subst_comp_on,
        wk_up_subst, wk1_tail, tail_scons, up_subst_id, <- subst_id_on, subst_ren_wk, eq_upwk.
    + intros Ξ ρΞ wfΞ u u' Ru.
      eapply irrLREq; [shelve|].
      rewrite ! Hsubst.
      unshelve eapply Vhf; tea.
      unshelve eapply consEllSubst, irrEll, Ru.
      now eapply wkSubst.
      Unshelve. fold ℓf. rewrite subst_ren_subst_up. f_equal.
      rewrite up_subst_comp.
      now unshelve erewrite <- subst_comp_on, <- up_subst_wk_up_wk1, wk_subst_comp_on,
        wk_up_subst, wk1_tail, tail_scons, up_subst_id, <- subst_id_on, subst_ren_wk, eq_upwk.
    + now unshelve eapply Vb.
    + erewrite <- subst_nat_to_term, subst_eval, subst_app.
      unshelve eapply Vtkb.
      now eapply lrefl.
  Qed.


  Lemma boxcastt {t}: [Γ ||-vEll< l > t : _ | _ | Vℓ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tTrue : _ | _ | VB] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓt (tBox ℓt (tEval ℓ t))) ≅ t : _ | _ | Vℓ].
  Proof.
    intros Vt Vtkt.
    etransitivity; cycle 1.
    + eapply etaEllValid, Vt.
    + unshelve eapply boxValid.
      1,2: tea.
      - eapply evalBoxValid.
        { now eapply evalValid. }
        intros n b [[-> ->] | [inb] ]%in_cons_ell_relevant; tea.
        now eapply evalnat_to_termValid.
      - intros n b inb.
        eapply evalnat_to_termValid.
        { eapply in_cons_ell; right; eapply inb. }
        unshelve eapply boxValid.
        1,2: tea.
        * now eapply evalValid.
        * clear n b inb.
          intros n b [[-> ->] | [inb] ]%in_cons_ell_relevant; tea.
          now eapply evalnat_to_termValid.
  Qed.

  Lemma boxcastf {t}: [Γ ||-vEll< l > t : _ | _ | Vℓ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tFalse : _ | _ | VB] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓf (tBox ℓf (tEval ℓ t))) ≅ t : _ | _ | Vℓ].
  Proof.
    intros Vt Vtkf.
    etransitivity; cycle 1.
    + eapply etaEllValid, Vt.
    + unshelve eapply boxValid.
      1,2: tea.
      - eapply evalBoxValid.
        { now eapply evalValid. }
        intros n b [[-> ->] | [inb] ]%in_cons_ell_relevant; tea.
        now eapply evalnat_to_termValid.
      - intros n b inb.
        eapply evalnat_to_termValid.
        { eapply in_cons_ell; right; eapply inb. }
        unshelve eapply boxValid.
        1,2: tea.
        * now eapply evalValid.
        * clear n b inb.
          intros n b [[-> ->] | [inb] ]%in_cons_ell_relevant; tea.
          now eapply evalnat_to_termValid.
  Qed.


  Lemma ellElimTrueValid {P P' ht ht' hf hf' t t'} (VP : [Γ,, ℓ ||-v< l > P ≅ P' | validSnocℓ VΓ Vℓ])
    (Vt : [Γ ||-vEll< l > t ≅ t' : _ | _ | Vℓ ]) :
    [Γ,, ℓt ||-v< l > ht ≅ ht' : P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..]
      | VΓt | substEllS (wkValidTy _ _ _ VP) boxEvalℓtValid ] ->
    [Γ,, ℓf ||-v< l > hf ≅ hf' : P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]
      | VΓf | substEllS (wkValidTy _ _ _ VP) boxEvalℓfValid ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tTrue : _ | _ | VB] ->
    [Γ ||-v< l > tEllElim k ℓ P ht hf t tTrue ≅ ht[(tBox ℓt (tEval ℓ t))..] : P[t..] | VΓ | substEllS VP Vt ].
  Proof.
    intros Vht Vhf Vtkt.
    unshelve eapply redSubstValid, lrefl, irrValidTm, substEllSTm, Vht.
    - eapply l.
    - now eapply lrefl.
    - exact (tBox ℓt (tEval ℓ t')).
    - eapply boxValid. { eapply evalValid, Vt. }
      intros n b [[-> ->] | []]%in_cons_ell_relevant; tea.
      eapply evalnat_to_termValid; tea. now eapply lrefl.
    - constructor; intros.
      rewrite <- subst_ellElim, ! subst_ren_subst_up, <- subst_box, <- subst_eval.
      eapply (liftEllSubst' Vℓ) in Vσσ' as Vℓσ.
      eapply (liftEllSubst' Vℓt) in Vσσ' as Vℓtσ.
      eapply (liftEllSubst' Vℓf) in Vσσ' as Vℓfσ.
(*       instValid Vσσ'; instValid Vℓσ; instValid Vℓtσ; instValid Vℓfσ; escape. *)
      eapply redtm_ellElimTrue; tea.
      + now instValid Vℓσ; escape.
      + instValid Vℓtσ; escape. clear -EscLRVht. fold ℓt.
        now erewrite subst_ren_subst_up, <- up_subst_wk_up_wk1 in EscLRVht.
      + instValid Vℓfσ; escape. clear -EscLRVhf. fold ℓf.
        now erewrite subst_ren_subst_up, <- up_subst_wk_up_wk1 in EscLRVhf.
      + now instValid Vσσ'; escape.
      + instValid Vσσ'; escape.
        erewrite <- subst_nat_to_term. eapply EscRVtkt.
    - rewrite to_subst_sound with (t := _[_]), subst_ren_subst_up.
      replace P⟨_⟩[_] with P
        by now rewrite wk_subst_comp_on, wk_up_subst, wk1_tail, tail_scons, up_subst_id, <- subst_id_on.
      unshelve eapply substEllS.
      1,2 : exact ℓ.
      1 : now eapply convValidEll.
      1: eapply lrefl, convValidTy, VP.
      cbn.
      eapply irrValidEllTmRfl, boxcastt, Vtkt; tea.
      now eapply lrefl.
  Qed.


  Lemma ellElimFalseValid {P P' ht ht' hf hf' t t'} (VP : [Γ,, ℓ ||-v< l > P ≅ P' | validSnocℓ VΓ Vℓ])
    (Vt : [Γ ||-vEll< l > t ≅ t' : _ | _ | Vℓ ]) :
    [Γ,, ℓt ||-v< l > ht ≅ ht' : P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..]
      | VΓt | substEllS (wkValidTy _ _ _ VP) boxEvalℓtValid ] ->
    [Γ,, ℓf ||-v< l > hf ≅ hf' : P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]
      | VΓf | substEllS (wkValidTy _ _ _ VP) boxEvalℓfValid ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tFalse : _ | _ | VB] ->
    [Γ ||-v< l > tEllElim k ℓ P ht hf t tFalse ≅ hf[(tBox ℓf (tEval ℓ t))..] : P[t..] | VΓ | substEllS VP Vt ].
  Proof.
    intros Vht Vhf Vtkf.
    unshelve eapply redSubstValid, lrefl, irrValidTm, substEllSTm, Vhf.
    - eapply l.
    - now eapply lrefl.
    - exact (tBox ℓf (tEval ℓ t')).
    - eapply boxValid. { eapply evalValid, Vt. }
      intros n b [[-> ->] | []]%in_cons_ell_relevant; tea.
      eapply evalnat_to_termValid; tea. now eapply lrefl.
    - constructor; intros.
      rewrite <- subst_ellElim, ! subst_ren_subst_up, <- subst_box, <- subst_eval.
      eapply (liftEllSubst' Vℓ) in Vσσ' as Vℓσ.
      eapply (liftEllSubst' Vℓt) in Vσσ' as Vℓtσ.
      eapply (liftEllSubst' Vℓf) in Vσσ' as Vℓfσ.
(*       instValid Vσσ'; instValid Vℓσ; instValid Vℓtσ; instValid Vℓfσ; escape. *)
      eapply redtm_ellElimFalse; tea.
      + now instValid Vℓσ; escape.
      + instValid Vℓtσ; escape. clear -EscLRVht. fold ℓt.
        now erewrite subst_ren_subst_up, <- up_subst_wk_up_wk1 in EscLRVht.
      + instValid Vℓfσ; escape. clear -EscLRVhf. fold ℓf.
        now erewrite subst_ren_subst_up, <- up_subst_wk_up_wk1 in EscLRVhf.
      + now instValid Vσσ'; escape.
      + instValid Vσσ'; escape.
        erewrite <- subst_nat_to_term. eapply EscRVtkf.
    - rewrite to_subst_sound with (t := _[_]), subst_ren_subst_up.
      replace P⟨_⟩[_] with P
        by now rewrite wk_subst_comp_on, wk_up_subst, wk1_tail, tail_scons, up_subst_id, <- subst_id_on.
      unshelve eapply substEllS.
      3 : eapply convValidEll, Vℓ.
      1: eapply lrefl, convValidTy, VP.
      eapply irrValidEllTmRfl, boxcastf, Vtkf.
      now eapply lrefl.
  Qed.

End ellElimValid.

End Ell.

Section Xi.
  Context `{GenericTypingProperties}.


  Lemma nSuccValid {Γ Γ' l k n n'} (VΓ : [||-v Γ ≅ Γ'])
    (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
    [Γ ||-v<l> nSucc k n ≅ nSucc k n' : tNat | VΓ | natValid VΓ].
  Proof.
    induction k; tea. cbn.
    now eapply succValid.
  Qed.


  Lemma xiLeafValid {Γ Γ' l k ℓ} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > tXi ℓ (nat_to_term k) ≅ tLeaf (nat_to_term k) : _ | _ |treeValid VΓ].
  Proof.
    eapply redSubstValid, leafValid, nSuccValid, zeroValid.
    constructor; intros.
    rewrite <- subst_xi, <- subst_leaf, ! subst_nat_to_term.
    now eapply redtm_xiLeaf.
  Qed.

  Lemma headevalrelnat_to_term ℓ k v : head (tApp (tEval ℓ (tRel v)) (nat_to_term k)) = Some (k, v).
  Proof.
    cbn. change (k, v) with (0+ k, v).
    generalize 0 as n.
    induction k; intros n.
    + now rewrite <- plus_n_O.
    + rewrite <- plus_n_Sm. eapply IHk.
  Qed.

  Lemma headalphanSucc i k t : whne t -> head (tApp (tAlpha i) (nSucc k t)) = head t.
  Proof.
    intros net.
    cbn.
    generalize 0 as n.
    induction k.
    + inversion net; subst; reflexivity.
    + cbn. easy.
  Qed.

  Lemma headevalrelnSucc ℓ k v t : whne t -> head (tApp (tEval ℓ (tRel v)) (nSucc k t)) = head t.
  Proof.
    intros net.
    cbn.
    generalize 0 as n.
    induction k.
    + inversion net; subst; reflexivity.
    + cbn. easy.
  Qed.

  Lemma subst_Alpha {n} {σ : substitution} : tAlpha (subst_alpha σ n) = (tAlpha n)[σ].
  Proof. reflexivity. Qed.

  Lemma whne_up_subst {m k σ} : whne m -> head m = Some (k, 0) ->
    whne m[up_subst σ] × head m[up_subst σ] = Some (k, 0).
  Proof.
    intros nem em.
    induction nem in k, em |- *; try solve [inversion em |
      specialize (IHnem _ em) as [IHne IHe]; split; tea; now constructor].
    + rewrite headevalrelnat_to_term in em. inversion em; subst; clear em.
      rewrite <- subst_app, <- subst_eval, subst_nat_to_term.
      split.
      - now eapply whne_tEvalRel.
      - eapply headevalrelnat_to_term.
    + inversion nem; subst; try solve [inversion em].
    + rewrite headalphanSucc in em by eapply nem.
      specialize (IHnem _ em) as [IHne IHe].
      split.
      - rewrite <- subst_app, <- subst_Alpha, subst_nSucc.
        now constructor.
      - now rewrite <- subst_app, <- subst_Alpha, subst_nSucc,
          headalphanSucc by eapply IHne.
    + rewrite headevalrelnSucc in em by eapply nem.
      specialize (IHnem _ em) as [IHne IHe].
      split.
      - rewrite <- subst_app, <- subst_eval, subst_nSucc.
  Abort.


  Lemma xiNodeValid {Γ Γ' l m ℓ k i} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ)
    (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) :
    whne m -> head m = Some (newnat_nat _ k, 0) ->
    [Γ,, ℓ ||-v< l > m : _ | _ | natValid VΓℓ] ->
    [Γ ||-v< l > tXi ℓ (nSucc i m) ≅ tNode (nat_to_term k) (tXi ℓt (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
        (tXi ℓf (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]) : _ | _ |treeValid VΓ].
  Proof.
    intros nem em Vm.
    constructor; intros.
    eapply redSubstValid, nodeValid.
    + constructor; intros.
      erewrite <- subst_node, <-! subst_xi, ! subst_ren_subst_up,
        <-! subst_box, <-! subst_eval, <-! up_subst_wk_up_wk1, subst_nSucc,
          subst_nat_to_term.
      eapply redtm_xiNode; tea.
      - eapply (liftEllSubst' Vℓ) in Vσσ' as Vℓσ.
        now instValid Vℓσ; escape.
      - 
  Admitted.


  Lemma Idnat_to_termValid {Γ Γ' l k} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > tId tNat (nat_to_term k) (nat_to_term k) | VΓ].
  Proof.
    eapply IdValid; eapply nSuccValid, zeroValid.
  Qed.

  Lemma xxiLeafValid {Γ Γ' l k ℓ n} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-vEll< l > n : ℓ | _ | ellValid VΓ] ->
    [Γ ||-v< l > tXXi ℓ (nat_to_term k) n ≅ tRefl tNat (nat_to_term k) : tId tNat (nat_to_term k) (nat_to_term k) | _ |Idnat_to_termValid VΓ].
  Proof.
    intros Vn.
    eapply redSubstValid, reflValid, nSuccValid, zeroValid.
    constructor; intros.
    rewrite <- subst_xxi, <- subst_Id, <- subst_refl, ! subst_nat_to_term.
    instValid Vσσ'; escape.
    now eapply redtm_xxiLeaf.
  Qed.


End Xi.

















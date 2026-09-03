From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties Introductions.Ell.
From LogRel.Validity Require Import Validity Irrelevance Properties ValidityTactics.
From LogRel.Validity.Introductions Require Import Bool Nat Tree Id SimpleArr.

Generalizable All Variables.

Section Ell.
  Context `{GenericTypingProperties}.


  Lemma NtoBValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v< l > arr' Γ tNat tBool ≅ arr' Γ tNat tBool | VΓ ].
  Proof.
    eapply simpleArr'Valid.
    + eapply natValid.
    + eapply boolValid.
  Defined.

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

  Lemma evalValid {Γ Γ' l ℓ t t'} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-vEll< l> t ≅ t' : ℓ | VΓ | ellValid VΓ] ->
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

  Lemma evalBoxValid {Γ Γ' l t n} {ℓ : ell} (VΓ: [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > t : _ | _ | NtoBValid VΓ] ->
    (forall k b, in_ell ℓ k b ->
      [Γ ||-v< l > tApp t (nat_to_term k) ≅ bool_to_term b : _ | _ | boolValid VΓ]) ->
    [Γ ||-v< l > tApp (tEval ℓ (tBox ℓ t)) (nat_to_term n) ≅ tApp t (nat_to_term n) : _ | _ | boolValid VΓ].
  Proof.
    intros Vt Vtkb.
    constructor; intros.
    rewrite <-! subst_app, <- subst_eval, <- subst_box, ->! subst_nat_to_term.
    etransitivity.
    + eapply appEvalBoxRedEq.
      - instValid Vσσ'. now eapply irrLR.
      - intros k b ink.
        specialize (Vtkb _ _ ink).
        erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
        instValid Vσσ'. now eapply irrLR.
    + eapply SimpleArr.simple_appcongTerm.
      - instValid Vσσ'. eapply RVt.
      - now unshelve eapply Nat.nat_to_termReq.
  Qed.


  Lemma castEllValid {Γ Γ' l} {ℓ ℓ': ell} {t} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > t : _ | _ | NtoBValid VΓ] ->
    (forall n b, in_ell ℓ n b -> [Γ ||-v< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | _ | boolValid VΓ]) ->
    (forall n b, in_ell ℓ' n b -> [Γ ||-v< l > tApp t (nat_to_term n) ≅ bool_to_term b : _ | _ | boolValid VΓ]) ->
    [Γ ||-v< l > tEval ℓ (tBox ℓ t) ≅ tEval ℓ' (tBox ℓ' t) : _ | _ | NtoBValid VΓ].
  Proof.
    intros Vt Vtℓ Vtℓ'.
    constructor; intros.
    rewrite <-! subst_eval, <-! subst_box.
    etransitivity.
    + unshelve eapply irrLR, castEllRed; tea.
      - instValid Vσσ'. now eapply irrLR.
      - intros n b inn.
        specialize (Vtℓ _ _ inn).
        erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
        instValid Vσσ'. now eapply irrLR.
      - intros n b inn.
        specialize (Vtℓ' _ _ inn).
        erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
        instValid Vσσ'. now eapply irrLR.
    + unshelve eapply irrLR, evalRedEq, boxRed; tea.
      - instValid Vσσ'. now eapply irrLR.
      - intros n b inn.
        specialize (Vtℓ' _ _ inn).
        erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_app.
        instValid Vσσ'. now eapply irrLR.
  Qed.

  Lemma boxEvalValid {Γ Γ' l} {ℓ ℓ' : ell} {t t'} (VΓ : [||-v Γ ≅ Γ']) :
    ℓ' ≤ε ℓ ->
    [Γ ||-vEll< l > t ≅ t' : ℓ' | VΓ | ellValid _] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓ' t) ≅ tBox ℓ (tEval ℓ' t') : ℓ | VΓ | ellValid _].
  Proof.
    intros ρε Vt.
    eapply boxValid.
    - now eapply evalValid.
    - intros n b inn.
      eapply evalnat_to_termValid, lrefl, Vt.
      now eapply ρε.
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
    eapply boxEvalValid, var0EllValid'.
    eapply Fwk_Fstep, Fwk_id.
  Qed.

  Let boxEvalℓfValid : [Γ,, ℓf ||-vEll< l > tBox ℓ (tEval ℓf (tRel 0)) : ℓ | VΓf | ellValid _].
  Proof.
    eapply boxEvalValid, var0EllValid'.
    eapply Fwk_Fstep, Fwk_id.
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

  Lemma castEtaEllValid {ℓ': ell} {t}
    (Vℓ' := ellValid (l:=l) (ℓ:=ℓ) VΓ) :
    [Γ ||-vEll< l > t : ℓ | _ | Vℓ ] ->
    (forall n b, in_ell ℓ' n b -> [Γ ||-v< l > tApp (tEval ℓ t) (nat_to_term n) ≅ bool_to_term b : _ | _ | VB]) ->
    ℓ' ≤ε ℓ ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓ' (tBox ℓ' (tEval ℓ t))) ≅ t : ℓ | _ | Vℓ].
  Proof.
    intros Vt Vtnb ρε.
    econstructor; intros.
    do 2 rewrite <- subst_box, <- subst_eval.
    etransitivity.
    + unshelve eapply irrEll, castEtaEllRed; tea.
      - instValid Vσσ'.
        eapply irrEll; tea. Unshelve.
      - intros n b inn; tea.
        specialize (Vtnb _ _ inn).
        instValid Vσσ'.
        erewrite <- subst_nat_to_term, <- subst_bool_to_term, subst_eval, subst_app.
        eapply irrLR; tea. Unshelve.
    + instValid Vσσ'.
      eapply irrEll; tea.
  Qed.


  Lemma boxcastt {t}: [Γ ||-vEll< l > t : _ | _ | Vℓ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tTrue : _ | _ | VB] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓt (tBox ℓt (tEval ℓ t))) ≅ t : _ | _ | Vℓ].
  Proof.
    intros Vt Vtkt.
    eapply castEtaEllValid, Fwk_Fstep, Fwk_id; tea.
    intros n b [[-> ->] | [inb] ]%in_cons_ell_relevant; tea.
    now eapply evalnat_to_termValid.
  Qed.

  Lemma boxcastf {t}: [Γ ||-vEll< l > t : _ | _ | Vℓ] ->
    [Γ ||-v< l > (tApp (tEval ℓ t) (nat_to_term k)) ≅ tFalse : _ | _ | VB] ->
    [Γ ||-vEll< l > tBox ℓ (tEval ℓf (tBox ℓf (tEval ℓ t))) ≅ t : _ | _ | Vℓ].
  Proof.
    intros Vt Vtkf.
    eapply castEtaEllValid, Fwk_Fstep, Fwk_id; tea.
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
    rewrite <- subst_xi, <- subst_leaf, subst_nat_to_term, subst_nSucc.
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

  Lemma headevalnSucc ℓ k u t : whne t -> head (tApp (tEval ℓ u) (nSucc k t)) = head t.
  Proof.
    intros net.
    cbn.
    generalize 0 as n.
    induction k.
    + destruct u; inversion net; subst; reflexivity.
    + cbn. easy.
  Qed.

  Lemma headxinSucc ℓ t k v kv : whne t -> head t = Some (kv, S v) -> head (tXi ℓ (nSucc k t)) = Some (kv, v).
  Proof.
    intros net et.
    cbn.
    generalize 0 as n.
    induction k.
    + intros n.
      inversion net; subst; clear net; eapply (f_equal headXi_aux et).
    + cbn. easy.
  Qed.

  Lemma headxxinSucc ℓ t k v kv u : whne t -> head t = Some (kv, S v) -> head (tXXi ℓ (nSucc k t) u) = Some (kv, v).
  Proof.
    intros net et.
    cbn.
    generalize 0 as n.
    induction k.
    + intros n.
      inversion net; subst; clear net; eapply (f_equal headXi_aux et).
    + cbn. easy.
  Qed.

(*   Lemma headevalrelnSucc ℓ k v t : whne t -> head (tApp (tEval ℓ (tRel v)) (nSucc k t)) = head t.
  Proof.
    intros net.
    cbn.
    generalize 0 as n.
    induction k.
    + inversion net; subst; reflexivity.
    + cbn. easy.
  Qed.
 *)
  Lemma subst_Alpha {n} {σ : substitution} : tAlpha (subst_alpha σ n) = (tAlpha n)[σ].
  Proof. reflexivity. Qed.

  Lemma whne_head_subst {m k σ v v'} : whne m -> head m = Some (k, v) -> (tRel v)[σ] = tRel v' ->
    whne m[σ] × head m[σ] = Some (k, v').
  Proof.
    intros nem em substv.
    induction nem in σ, v, v', substv, k, em |- *; try solve [inversion em |
      specialize (IHnem _ _ _ _ em substv) as [IHne IHe]; split; tea; now constructor].
    + rewrite headevalrelnat_to_term in em. inversion em; subst; clear em.
      rewrite <- subst_app, <- subst_eval, subst_nat_to_term, substv.
      split.
      - now eapply whne_tEvalRel.
      - eapply headevalrelnat_to_term.
    + inversion nem; subst; try solve [inversion em].
    + rewrite headalphanSucc in em by tea.
      specialize (IHnem _ _ _ _ em substv) as [IHne IHe].
      rewrite <- subst_app, <- subst_Alpha, subst_nSucc.
      rewrite headalphanSucc by tea.
      split; tea.
      now constructor.
    + rewrite headevalnSucc in em by eapply nem.
      specialize (IHnem _ _ _ _ em substv) as [IHne IHe].
      rewrite <- subst_app, <- subst_eval, subst_nSucc.
      rewrite headevalnSucc by tea.
      split; tea.
      now constructor.
    + erewrite headxinSucc in em by tea.
      inversion em; subst; clear em.
      specialize (IHnem _ (up_subst σ) (S v) (S v') e
        (f_equal (ren_term shift) substv)) as [IHne IHe].
      rewrite <- subst_xi, subst_nSucc.
      erewrite headxinSucc by tea.
      split; now econstructor.
    + erewrite headxxinSucc in em by tea.
      inversion em; subst; clear em.
      specialize (IHnem _ (up_subst σ) (S v) (S v') e
        (f_equal (ren_term shift) substv)) as [IHne IHe].
      rewrite <- subst_xxi, subst_nSucc.
      erewrite headxxinSucc by tea.
      split; now econstructor.
  Qed.

  Lemma whne_up_subst {m k σ} : whne m -> head m = Some (k, 0) ->
    whne m[up_subst σ] × head m[up_subst σ] = Some (k, 0).
  Proof.
    intros nem em.
    now eapply whne_head_subst.
  Qed.


  Lemma xiValid {Γ Γ' l m m' ℓ} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ) :
    [Γ,, ℓ ||-v< l > m ≅ m' : _ | _ | natValid VΓℓ] ->
    [Γ ||-v< l > tXi ℓ m ≅ tXi ℓ m' : _ | _ |treeValid VΓ].
  Proof. Admitted.

  Lemma xiNodeValid {Γ Γ' l m ℓ k i} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ)
    (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) :
    whne m -> head m = Some (newnat_nat _ k, 0) ->
    [Γ,, ℓ ||-v< l > m : _ | _ | natValid VΓℓ] ->
    [Γ ||-v< l > tXi ℓ (nSucc i m) ≅ tNode (nat_to_term k) (tXi ℓt (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
        (tXi ℓf (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]) : _ | _ |treeValid VΓ].
  Proof.
    intros nem em Vm.
    eapply redSubstValid, lrefl, nodeValid.
    + constructor; intros.
      erewrite <- subst_node, <-! subst_xi, ! subst_ren_subst_up,
        <-! subst_box, <-! subst_eval, <-! up_subst_wk_up_wk1, subst_nSucc,
          subst_nat_to_term.
      specialize (whne_up_subst (σ:=σ) nem em) as [nemσ emσ].
      eapply redtm_xiNode; tea.
      eapply (liftEllSubst' Vℓ) in Vσσ' as Vℓσ.
      now instValid Vℓσ; escape.
    + eapply nSuccValid, zeroValid.
    + eapply xiValid.
      rewrite wk_nSucc, to_subst_sound, subst_nSucc, <- to_subst_sound.
      unshelve now eapply nSuccValid, irrValidTmRfl, substEllSTm, wkValidTm; tea.
      2,3 : shelve.
      - unshelve eapply validSnocℓ, ellValid; tea.
      - eapply ellValid.
      - unshelve eapply boxValid.
        1,2: shelve.
        * eapply boolValid.
        * eapply evalValid, var0EllValid'.
        * intros n b inn.
          eapply evalnat_to_termValid, var0EllValid'.
          now eapply in_cons_ell.
    + eapply xiValid.
      rewrite wk_nSucc, to_subst_sound, subst_nSucc, <- to_subst_sound.
      unshelve now eapply nSuccValid, irrValidTmRfl, substEllSTm, wkValidTm; tea.
      2,3: shelve.
      - unshelve eapply validSnocℓ, ellValid; tea.
      - eapply ellValid.
      - unshelve eapply boxValid.
        1,2: shelve.
        * eapply boolValid.
        * unshelve eapply evalValid, var0EllValid'.
        * intros n b inn.
          eapply evalnat_to_termValid, var0EllValid'.
          now eapply in_cons_ell.
  Qed.


  Lemma Idnat_to_termValid {Γ Γ' l k} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > tId tNat (nat_to_term k) (nat_to_term k) | VΓ].
  Proof.
    eapply IdValid; eapply nSuccValid, zeroValid.
  Qed.

  Lemma xxiLeafValid {Γ Γ' l k ℓ n} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-vEll< l > n : ℓ | _ | ellValid VΓ] ->
    [Γ ||-v< l > tXXi ℓ (nat_to_term k) n ≅ tRefl tNat (nat_to_term k) :
      tId tNat (nat_to_term k) (nat_to_term k) | _ |Idnat_to_termValid VΓ].
  Proof.
    intros Vn.
    eapply redSubstValid, reflValid, nSuccValid, zeroValid.
    constructor; intros.
    rewrite <- subst_xxi, <- subst_Id, <- subst_refl, ! subst_nat_to_term.
    instValid Vσσ'; escape.
    now eapply redtm_xxiLeaf.
  Qed.

  Lemma xxiTyValid {Γ Γ' l t t' u u'} {ℓ : ell} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ,, ℓ ||-v< l > t ≅ t': tNat | validSnocℓ (l:=l) VΓ (ellValid VΓ) | natValid _ ] ->
    [ Γ ||-vEll< l > u ≅ u' : ℓ | _ | ellValid VΓ] ->
    [Γ ||-v< l > tId tNat (dEval' Γ (tXi ℓ t) (tEval ℓ u)) t[u..] | VΓ].
  Proof.
    intros Vt Vu.
    unshelve eapply IdValid, irrValidTmRfl, substEllSTm, lrefl.
    1-6,10 : shelve.
    + eapply ellValid.
    + eapply natValid.
    + eapply lrefl, Vu.
    + eapply dEval'Valid, irrValidTmRfl, evalValid, lrefl, Vu.
      - eapply xiValid, lrefl, Vt.
      - reflexivity.
    + reflexivity.
    + eapply Vt.
  Qed.

  Lemma xxiValid {Γ Γ' l m m' n n' ℓ} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ)
    (Vm : [Γ,, ℓ ||-v< l > m ≅ m' : _ | _ | natValid VΓℓ])
    (Vn : [ Γ ||-vEll< l > n ≅ n' : ℓ | _ | ellValid VΓ]) :
    [Γ ||-v< l > tXXi ℓ m n ≅ tXXi ℓ m' n' : _ | _ |xxiTyValid VΓ Vm Vn].
  Proof. Admitted.

  Lemma xxiNodeTyValid {Γ Γ' l m n ℓ i} (VΓ : [||-v Γ ≅ Γ']) 
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ):
    [Γ,, ℓ ||-v< l > m : _ | _ | natValid VΓℓ] ->
    [Γ ||-vEll< l > n : ℓ | _ | ellValid VΓ] ->
    [_ ||-v< l > tId tNat (dEval' Γ (tXi ℓ (nSucc i m)) (tEval ℓ n)) (nSucc i m)[n..] | VΓ].
  Proof.
    intros Vm Vn.
    eapply xxiTyValid, Vn.
    now eapply nSuccValid.
  Qed.

  Lemma wk_subst_ass `(ρ : Ξ ≤ Δ) σ τ : σ ∘s (τ ∘r ρ) = (σ ∘s τ) ∘r ρ.
  Proof. reflexivity. Qed.

  Lemma idtermValid `(VΓ : [||-v Γ ≅ Γ']) `(VA : [Γ ||-v< l > A ≅ A' | VΓ]) :
    [Γ ||-v< l > idterm A ≅ idterm A' : _ | VΓ | simpleArr'Valid _ VA VA].
  Proof.
    now unshelve eapply irrValidTmRfl, Lambda.lamCongValid, Var.var0Valid.
  Qed.

  Lemma idtermValid' `(VΓ : [||-v Γ ≅ Γ']) `(VAtoA : [Γ ||-v< l > arr' Γ A A ≅ arr' Γ A' A' | VΓ]) :
    [Γ ||-v< l > idterm A ≅ idterm A' : _ | VΓ | VAtoA].
  Proof.
    unshelve eapply irrValidTmRfl, idtermValid; tea.
    - eapply Pi.validΠdom, VAtoA.
    - reflexivity.
  Qed.


  Lemma simpleBetaValid {t a}
    `(VΓ : [||-v Γ ≅ Γ'])
    `(VF : [Γ ||-v< l > F | VΓ ])
    `(VG : [Γ ||-v< l > G | VΓ ])
    (Vt : [Γ ,, F ||-v<l> t : _ | _ | wk1ValidTy VF VG])
    (Va : [Γ ||-v<l> a : F | VΓ | VF]) :
    [Γ ||-v<l> tApp (tLambda F t) a ≅ t[a..] : G | VΓ | VG].
  Proof.
    unshelve eapply irrValidTmRfl, Lambda.betaValid, Vt.
    1:shelve.
    eapply Va.
    eapply shift_subst1.
  Qed.

(*   Lemma treeElim'NodeValid `(VΓ : [||-vΓ ≅ Γ']) 
    (VP : [Γ,, tTree ||-v< l > P ≅ P | validSnoc VΓ (treeValid VΓ)]) :
    (P' := ⟨wk_up tTree (wk1 tNat)⟩⟨wk_up tTree (wk1 tTree)⟩⟨
           wk_up tTree (wk1 tTree)⟩)
    (hl' := tLambda tNat hl)
    (hn' := (tLambda tNat (tLambda tTree (tLambda tTree (tLambda P'[(tRel 1)..] (tLambda P'[(tRel 0)..]⟨@wk1  hn))))).
    [Γ,, tNat ||-v< l > hl ≅ hl : P⟨wk_up tTree (wk1 tNat)⟩[(tLeaf (tRel 0))..] | VΓ | elimLeafHypTyValid VΓ VP]
    [Γ ||-v< l > tTreeElim P hl' hn'
      (tNode n dt df) ≅ hn[n.: dt .: df .: (tTreeElim P hl' hn' dt) .: (tTreeElim P hl' hn' df)..]. *)

  Lemma lamValid' {t t' l} `(VΓ : [||-v Γ ≅ Γ'])
    `(VΠFG : [ Γ ||-v< l > tProd F G ≅ tProd F' G' | VΓ]) :
    [Γ,, F ||-v< l > t ≅ t' : G | validSnoc VΓ _ | Pi.validΠcod VΠFG] ->
    [Γ ||-v< l > tLambda F t ≅ tLambda F' t' :
      tProd F G | VΓ | VΠFG ].
  Proof.
    intros Vt.
    eapply irrValidTmRfl, Lambda.lamCongValid, Vt.
    reflexivity.
  Qed.


  Lemma shift_to_subst1 {Γ : context} {A : decl} {B a : term} : B⟨@wk1 Γ A⟩[to_subst (a..)] = B.
  Proof. now rewrite <- to_subst_sound, shift_subst1. Qed.

  Lemma dEval'NodeValid {Γ Γ' l n f dt df} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > f :_ | VΓ | NtoBValid _] ->
    [Γ ||-v< l > n :_ | VΓ | natValid _] ->
    [Γ ||-v< l > dt :_ | VΓ | treeValid _] ->
    [Γ ||-v< l > df :_ | VΓ | treeValid _] ->
    [Γ ||-v< l > dEval' Γ (tNode n dt df) f ≅ tBoolElim tNat (dEval' Γ dt f) (dEval' Γ df f) (tApp f n) : _ | VΓ | natValid _].
  Proof.
    intros Vf Vn Vdt Vdf.
    assert (VΓN : [||-v Γ,, tNat ≅ _]) by now unshelve eapply validSnoc, natValid.
    assert (VΓNT : [||-v Γ,, tNat,, tTree ≅ _]) by (unshelve eapply validSnoc, treeValid; [|tea..]).
    assert (VΓNTT : [||-v Γ,, tNat,, tTree,, tTree ≅ _]) by (unshelve eapply validSnoc, treeValid; [|tea..]).
    assert (VΓNTTN : [||-v Γ,, tNat,, tTree,, tTree,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓNTTNN : [||-v Γ,, tNat,, tTree,, tTree,, tNat,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓNTTNNB : [||-v Γ,, tNat,, tTree,, tTree,, tNat,, tNat,, tBool ≅ _])
      by (unshelve eapply validSnoc, boolValid; [|tea..]).
    assert (VΓT : [||-v Γ,, tTree ≅ _]) by (unshelve eapply validSnoc, treeValid; [|tea..]).
    assert (VΓTT : [||-v Γ,, tTree,, tTree ≅ _]) by (unshelve eapply validSnoc, treeValid; [|tea..]).
    assert (VΓTTN : [||-v Γ,, tTree,, tTree,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓTTNN : [||-v Γ,, tTree,, tTree,, tNat,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓTTNNB : [||-v Γ,, tTree,, tTree,, tNat,, tNat,, tBool ≅ _])
      by (unshelve eapply validSnoc, boolValid; [|tea..]).
    assert (VΓTN : [||-v Γ,, tTree,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓTNN : [||-v Γ,, tTree,, tNat,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓTNNB : [||-v Γ,, tTree,, tNat,, tNat,, tBool ≅ _])
      by (unshelve eapply validSnoc, boolValid; [|tea..]).
    assert (VΓNN : [||-v Γ,, tNat,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [|tea..]).
    assert (VΓNNB : [||-v Γ,, tNat,, tNat,, tBool ≅ _])
      by (unshelve eapply validSnoc, boolValid; [|tea..]).
    assert (Vfn : [Γ ||-v< l > tApp f n ≅ tApp f n : _ | VΓ | boolValid _]).
    { now eapply simple_app'Valid. }
    etransitivity.
    + unfold dEval'.
      unshelve eapply irrValidTmRfl, treeElimNodeValid, dEvalNode'Valid, Vf; tea.
      - reflexivity.
      - eapply idtermValid'.
    + unfold dEvalNode' at 1.
      etransitivity.
      unshelve eapply simple_app'Valid, treeElimValid, dEvalNode'Valid, Vf.
      1,3,4: shelve.
      { eapply simpleArr'Valid; eapply natValid. }
      { tea. }
      2: eapply idtermValid'.
      etransitivity.
      unshelve eapply simple_app'Valid, treeElimValid, dEvalNode'Valid, Vf.
      1,3,4: shelve.
      { eapply simpleArr'Valid, simpleArr'Valid; eapply natValid. }
      { tea. }
      2: eapply idtermValid'.
      etransitivity.
      unshelve eapply simple_app'Valid, Vdf.
      1:shelve.
      { eapply simpleArr'Valid, simpleArr'Valid, simpleArr'Valid;
        first [eapply natValid|eapply treeValid]. }
      etransitivity.
      unshelve eapply simple_app'Valid, Vdt.
      1:shelve.
      { eapply simpleArr'Valid, simpleArr'Valid, simpleArr'Valid, simpleArr'Valid;
        first [eapply natValid|eapply treeValid]. }
      eapply simpleBetaValid; tea.
      repeat change (arr' ?Γ ?C ?D)⟨?ρ⟩ with (arr' (Γ,,tNat) C⟨ρ⟩ D⟨ρ⟩).
      repeat change tTree⟨_⟩ with tTree.
      repeat change tNat[_] with tNat.
      repeat change tNat⟨_⟩ with tNat.
      eapply lamValid', lamValid', lamValid', lamValid'.
      unshelve eapply irrValidTmRfl, boolElimCongValid, (Var.var0Valid' (A:=tNat)).
      { tea. }
      { eapply natValid. }
      { unshelve eapply simple_app'Valid, Var.varnValid.
        1,2: shelve.
        + eapply natValid.
        + eapply simpleArr'Valid, boolValid.
          eapply natValid.
        + rewrite ! wk_comp_ren_on.
          unshelve eapply irrValidTmRfl, wkValidTm, Vf; tea.
          reflexivity.
        + do 4 eapply in_there' with (A:=tNat); constructor. }
      { reflexivity. }
      { eapply (Var.var1Valid' (A:=tNat)). }
      rewrite to_subst_sound with (t:=tLambda _ _), <-! subst_lam,
        <- subst_boolElim, <- subst_app.
      rewrite <- (subst_up_wk1 (Δ := Γ,, tTree,, tTree,, tNat)),
        <- (subst_up_wk1 (Δ := Γ,, tTree,, tTree)),
        <- (subst_up_wk1 (Δ := Γ,, tTree)),
        <- (subst_up_wk1 (Δ := Γ)),
        shift_to_subst1.
      change tNat[_] with tNat; change tTree[_] with tTree;
        change (tRel 1)[_] with (tRel 1); change (tRel 0)[_] with (tRel 0).
      match goal with |- context C[f⟨?ρ1⟩⟨?ρ2⟩⟨?ρ3⟩⟨?ρ4⟩] =>
        replace (tRel 4)[_] with n⟨ρ1⟩⟨ρ2⟩⟨ρ3⟩⟨ρ4⟩ by now rewrite ! wk1_ren_on end.
      rewrite ! wk_app.
      eapply simpleBetaValid; tea.
      repeat change (arr' ?Γ ?C ?D)⟨?ρ⟩ with (arr' (Γ,,tNat) C⟨ρ⟩ D⟨ρ⟩).
      repeat change tTree⟨_⟩ with tTree.
      repeat change tNat[_] with tNat.
      repeat change tNat⟨_⟩ with tNat.
      eapply lamValid', lamValid', lamValid'.
      unshelve eapply irrValidTmRfl, boolElimCongValid, (Var.var0Valid' (A:=tNat)).
      { tea. }
      { eapply natValid. }
      { rewrite ! wk_comp_ren_on.
        unshelve eapply irrValidTmRfl, wkValidTm, Vfn; tea.
        reflexivity. }
      { reflexivity. }
      { eapply (Var.var1Valid' (A:=tNat)). }
      rewrite to_subst_sound with (t:=tLambda _ _), <-! subst_lam, <- subst_boolElim.
      rewrite <- (subst_up_wk1 (Δ := Γ,, tTree,, tNat)),
        <- (subst_up_wk1 (Δ := Γ,, tTree)),
        <- (subst_up_wk1 (Δ := Γ)),
        shift_to_subst1.
      change tNat[_] with tNat; change tTree[_] with tTree;
        change (tRel 1)[_] with (tRel 1); change (tRel 0)[_] with (tRel 0).
      eapply simpleBetaValid; tea.
      repeat change (arr' ?Γ ?C ?D)⟨?ρ⟩ with (arr' (Γ,,tNat) C⟨ρ⟩ D⟨ρ⟩).
      repeat change tTree⟨_⟩ with tTree.
      repeat change tNat[_] with tNat.
      repeat change tNat⟨_⟩ with tNat.
      eapply lamValid', lamValid'.
      unshelve eapply irrValidTmRfl, boolElimCongValid, (Var.var0Valid' (A:=tNat)).
      { tea. }
      { eapply natValid. }
      { rewrite ! wk_comp_ren_on.
        unshelve eapply irrValidTmRfl, wkValidTm, Vfn; tea.
        reflexivity. }
      { reflexivity. }
      { eapply (Var.var1Valid' (A:=tNat)). }
      rewrite to_subst_sound with (t:=tLambda _ _), <-! subst_lam, <- subst_boolElim.
      rewrite <- (subst_up_wk1 (Δ := Γ,, tNat)),
        <- (subst_up_wk1 (Δ := Γ)),
        shift_to_subst1.
      change tNat[_] with tNat; change tTree[_] with tTree;
        change (tRel 1)[_] with (tRel 1); change (tRel 0)[_] with (tRel 0).
      eapply simpleBetaValid.
      2:{ change tNat with tNat[dt..].
        unshelve eapply (treeElimCongValid _ (P:=tNat)), dEvalNode'Valid; tea.
        eapply idtermValid'. }
      repeat change (arr' ?Γ ?C ?D)⟨?ρ⟩ with (arr' (Γ,,tNat) C⟨ρ⟩ D⟨ρ⟩).
      repeat change tNat⟨_⟩ with tNat.
      eapply lamValid'.
      unshelve eapply irrValidTmRfl, boolElimCongValid, (Var.var0Valid' (A:=tNat)).
      { tea. }
      { eapply natValid. }
      { rewrite ! wk_comp_ren_on.
        unshelve eapply irrValidTmRfl, wkValidTm, Vfn; tea.
        reflexivity. }
      { reflexivity. }
      { eapply (Var.var1Valid' (A:=tNat)). }
      rewrite to_subst_sound with (t:=tLambda _ _), <-! subst_lam, <- subst_boolElim.
      rewrite <- (subst_up_wk1 (Δ := Γ)),
        shift_to_subst1.
      change tNat[_] with tNat; change tTree[_] with tTree;
        change (tRel 0)[_] with (tRel 0).
      replace (tRel 1)[_] with (dEval' Γ dt f)⟨@wk1 Γ tNat⟩ by now rewrite wk1_ren_on.
      change (tTreeElim _ _ _ _) with (dEval' Γ df f).
      eapply eq_rect.
      eapply simpleBetaValid, dEval'Valid; tea.
      2: now rewrite to_subst_sound, <- subst_boolElim, ! shift_to_subst1.
      unshelve eapply irrValidTmRfl, boolElimCongValid, (Var.var0Valid' (A:=tNat)); tea.
      { eapply natValid. }
      { unshelve eapply irrValidTmRfl, wkValidTm, Vfn; tea.
        reflexivity. }
      { reflexivity. }
      { unshelve eapply irrValidTmRfl, wkValidTm, dEval'Valid; tea.
        reflexivity. }
  Qed.


  Lemma dEval'XiValid {Γ Γ' l m n ℓ k i b} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ) (ℓb := cons_ell ℓ k b):
    [Γ,, ℓ ||-v< l > m : _ | VΓℓ | natValid _] ->
    [Γ ||-v< l > n : _ | VΓ | NtoBValid _ ] ->
    [Γ ||-v< l > tApp n (nat_to_term k) ≅ bool_to_term b : _ | VΓ | boolValid _] ->
    whne m -> head m = Some (k : nat, 0) ->
    [Γ ||-v< l > dEval' Γ (tXi ℓ (nSucc i m)) n ≅
      dEval' Γ (tXi ℓb (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓb)⟩[(tBox ℓ (tEval ℓb (tRel 0)))..]) n : _ | VΓ | natValid _ ].
  Proof.
    intros Vm Vn Vnkb nem em.
    assert (VΓℓb : forall b, [||-v Γ,, cons_ell ℓ k b ≅ Γ',, cons_ell ℓ k b]).
    { intros; now unshelve eapply validSnocℓ, ellValid. }
    assert (VXi : forall b (ℓb := cons_ell ℓ k b),
      [Γ ||-v< l > tXi ℓb (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓb)⟩
        [(tBox ℓ (tEval ℓb (tRel 0)))..] : _ | VΓ | treeValid _]).
    { clear dependent b; intros b ℓb.
      unshelve eapply xiValid, irrValidTmRfl, substEllSTm, wkValidTm, nSuccValid, Vm.
        2: shelve.
        * eapply VΓℓb.
        * eapply ellValid.
        * eapply boxEvalValid, var0EllValid'.
          eapply Fwk_Fstep, Fwk_id.
        * reflexivity. }
    etransitivity; [|etransitivity]; [..|etransitivity].
    + eapply dEval'Valid, Vn.
      eapply xiNodeValid; tea.
    + eapply dEval'NodeValid; tea.
      - eapply nSuccValid, zeroValid.
      - eapply VXi.
      - eapply VXi.
    + unshelve eapply irrValidTmRfl, boolElimCongValid.
      4-7: shelve.
      - tea.
      - eapply natValid.
      - eapply Vnkb.
      - reflexivity.
      - eapply irrValidTmRfl, dEval'Valid, Vn.
        * reflexivity.
        * eapply VXi.
      - eapply irrValidTmRfl, dEval'Valid, Vn.
        * reflexivity.
        * eapply VXi.
    + destruct b.
      - unshelve eapply irrValidTmRfl, boolElimTrueValid.
        2,4,5: shelve.
        * tea.
        * eapply natValid.
        * reflexivity.
        * eapply irrValidTmRfl, dEval'Valid, Vn.
         ++ reflexivity.
         ++ eapply VXi.
        * eapply irrValidTmRfl, dEval'Valid, Vn.
         ++ reflexivity.
         ++ eapply VXi.
      - unshelve eapply irrValidTmRfl, boolElimFalseValid.
        2,4,5: shelve.
        * tea.
        * eapply natValid.
        * reflexivity.
        * eapply irrValidTmRfl, dEval'Valid, Vn.
         ++ reflexivity.
         ++ eapply VXi.
        * eapply irrValidTmRfl, dEval'Valid, Vn.
         ++ reflexivity.
         ++ eapply VXi.
  Qed.



  Lemma xxiNodeValid {Γ Γ' l m n ℓ k i} (VΓ : [||-v Γ ≅ Γ'])
    (Vℓ := ellValid (l:=l) (ℓ:=ℓ) VΓ) (VΓℓ := validSnocℓ VΓ Vℓ)
    (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false)
    (Vm : [Γ,, ℓ ||-v< l > m : _ | _ | natValid VΓℓ])
    (Vn : [Γ ||-vEll< l > n : ℓ | _ | ellValid VΓ]):
    whne m -> head m = Some (newnat_nat _ k, 0) ->
    [Γ ||-v< l > tXXi ℓ (nSucc i m) n ≅ tEllElim k ℓ (tId tNat (dEval' (Γ,, ℓ)
              (tXi ℓ (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓ)⟩) (tEval ℓ (tRel 0))) (nSucc i m))
            (tXXi ℓt (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓt)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓt) ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] (tRel 0))
            (tXXi ℓf (nSucc i m)⟨wk_up ℓ (@wk1 Γ ℓf)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓf) ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] (tRel 0))
            n (tApp (tEval ℓ n) (nat_to_term k)) : _ | _ |xxiNodeTyValid VΓ (i:=i) Vm Vn].
  Proof.
    intros nem em.
    unshelve eapply redSubstValid, irrValidTmRfl, lrefl, ellElimValid.
    4-8: shelve.
    + tea.
    + eapply IdValid, nSuccValid, Vm.
      unshelve eapply dEval'Valid, irrValidTmRfl, evalValid, var0EllValid'; [shelve |tea| |reflexivity].
      rewrite wk_nSucc.
      unshelve eapply xiValid, nSuccValid, irrValidTmRfl, wkValidTm, Vm; [|reflexivity].
      unshelve eapply validSnocℓ, ellValid; tea.
    + eapply Vn.
    + constructor; intros.
      erewrite <- subst_ellElim, <-! subst_xxi, <-! subst_Id, ! subst_ren_subst_up,
        <-! subst_dEval', <- subst_app, <-! subst_box, <-! subst_eval,
        <-! subst_xi, <-! up_subst_wk_up_wk1, subst_nSucc, ! subst_nat_to_term.
      change (tRel 0)[_] with (tRel 0); change tNat[_] with tNat.
      specialize (whne_up_subst (σ:=σ) nem em) as [nemσ emσ].
      eapply (liftEllSubst' Vℓ) in Vσσ' as Vℓσ.
      instValid Vℓσ; instValid Vσσ'; escape.
      eapply redtm_xxiNode; tea.
    + erewrite ! to_subst_sound, <- subst_Id, <- subst_dEval', <- subst_xi.
      do 3 f_equal.
      now rewrite wk_subst_comp_on, wk_up_subst, wk1_tail,
        tail_scons, up_subst_id, <- subst_id_on.
    + unshelve eapply irrValidTm, xxiValid.
      1-2,7,8: shelve.
      1,2: tea.
      2: unshelve eapply validSnocℓ, ellValid; [|tea| now eapply lrefl].
      - now unshelve eapply validSnocℓ, ellValid.
      - rewrite ->! wk_nSucc, to_subst_sound, subst_nSucc, <- to_subst_sound.
        unshelve eapply nSuccValid, irrValidTmRfl, substEllSTm, wkValidTm, wkValidTm, Vm.
        2,3,6: shelve.
        * unshelve eapply validSnocℓ, ellValid; tea.
          unshelve eapply validSnocℓ, ellValid; tea.
        * eapply ellValid.
        * eapply boxEvalValid, var0EllValid'.
          eapply Fwk_Fstep, Fwk_id.
        * unshelve eapply validSnocℓ, ellValid; [shelve|tea|].
          unshelve eapply validSnocℓ, ellValid; tea.
        * reflexivity.
      - eapply var0EllValid'.
      - erewrite ! to_subst_sound, <-! wk_Id, <-! subst_Id.
        unshelve eapply IdValid.
        * eapply natValid.
        * symmetry. rewrite <- wk_dEval', <- (subst_dEval' (Δ:= Γ,, ℓt)).
          rewrite wk_xi. rewrite <- wk_up_wk1, shift_to_subst1.
          change (tEval ?ℓ _)⟨_⟩[_] with (tEval ℓ (tBox ℓ (tEval ℓt (tRel 0)))).
          rewrite <- wk_xi, wk_nSucc.
          etransitivity.
          unshelve eapply irrValidTmRfl, dEval'XiValid.
          2,3: shelve.
         ++ unshelve eapply validSnocℓ, ellValid; tea.
            now eapply lrefl.
         ++ reflexivity.
         ++ unshelve (eapply irrValidTm, wkValidTm, Vm; eapply natValid).
            3,4: unshelve eapply validSnocℓ, ellValid;
              [..|unshelve eapply validSnocℓ, ellValid]; tea.
            tea. now eapply lrefl.
         ++ eapply evalValid, boxEvalValid, var0EllValid'.
            eapply Fwk_Fstep, Fwk_id.
         ++ etransitivity.
           -- eapply simple_app'Valid, nSuccValid, zeroValid.
              eapply castEllValid.
             ** eapply evalValid, var0EllValid'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply in_cons_ell; right; eapply ink'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply ink'.
           -- eapply evalnat_to_termValid, boxEvalValid.
             ** eapply in_cons_ell; repeat constructor.
             ** eapply Fwk_id.
             ** eapply var0EllValid'.
         ++ eapply whne_ren_wl, nem.
         ++ now etransitivity; [eapply head_ren| rewrite em].
         ++ eapply dEval'Valid, PER_Transitive.
           -- eapply xiValid.
              rewrite <- to_subst_sound.
              unshelve eapply irrValidTmRfl, (substEllSTm (G:=tNat)).
              2-6: shelve.
             ** unshelve eapply validSnocℓ, ellValid; tea.
                unshelve eapply validSnocℓ, ellValid; tea.
                now eapply lrefl.
             ** eapply boxEvalValid, var0EllValid'.
                eapply Fwk_Fstep, Fwk_id.
             ** reflexivity.
             ** rewrite <- wk_nSucc, ! wk_comp_ren_on.
                eapply (wkValidTm (A:=tNat)), nSuccValid, Vm.
           -- eapply castEllValid.
             ** eapply evalValid, var0EllValid'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply in_cons_ell; right; tea.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'; tea.
           -- eapply evalValid, etaEllValid, var0EllValid'.
        * rewrite <- to_subst_sound with (t:= (nSucc _ _)⟨_⟩⟨_⟩), <-! to_subst_sound.
          rewrite subst_ren_subst_up, wk_subst_comp_on with (σ:= up_subst _).
          unshelve erewrite (subst_subst_eq (_ ∘r _) subst_id _ _⟨_⟩ _⟨_⟩ eq_refl), <- subst_id_on.
          { now rewrite wk_up_subst, wk1_tail, tail_scons, up_subst_id. }
          unshelve eapply irrValidTmRfl, (substEllSTm (G:=tNat)).
          2-6: shelve.
         ++ unshelve eapply validSnocℓ, ellValid; tea.
            now eapply lrefl.
         ++ eapply boxEvalValid, var0EllValid'.
            eapply Fwk_Fstep, Fwk_id.
         ++ reflexivity.
         ++ eapply (wkValidTm (A:=tNat)), nSuccValid, Vm.
    + unshelve eapply irrValidTm, xxiValid.
      1-2,7,8: shelve.
      1,2: tea.
      2: unshelve eapply validSnocℓ, ellValid; [|tea| now eapply lrefl].
      - now unshelve eapply validSnocℓ, ellValid.
      - rewrite ->! wk_nSucc, to_subst_sound, subst_nSucc, <- to_subst_sound.
        unshelve eapply nSuccValid, irrValidTmRfl, substEllSTm, wkValidTm, wkValidTm, Vm.
        2,3,6: shelve.
        * unshelve eapply validSnocℓ, ellValid; tea.
          unshelve eapply validSnocℓ, ellValid; tea.
        * eapply ellValid.
        * eapply boxEvalValid, var0EllValid'.
          eapply Fwk_Fstep, Fwk_id.
        * unshelve eapply validSnocℓ, ellValid; [shelve|tea|].
          unshelve eapply validSnocℓ, ellValid; tea.
        * reflexivity.
      - eapply var0EllValid'.
      - erewrite ! to_subst_sound, <-! wk_Id, <-! subst_Id.
        unshelve eapply IdValid.
        * eapply natValid.
        * symmetry. rewrite <- wk_dEval', <- (subst_dEval' (Δ:= Γ,, ℓf)).
          rewrite wk_xi. rewrite <- wk_up_wk1, shift_to_subst1.
          change (tEval ?ℓ _)⟨_⟩[_] with (tEval ℓ (tBox ℓ (tEval ℓf (tRel 0)))).
          rewrite <- wk_xi, wk_nSucc.
          etransitivity.
          unshelve eapply irrValidTmRfl, dEval'XiValid.
          2,3: shelve.
         ++ unshelve eapply validSnocℓ, ellValid; tea.
            now eapply lrefl.
         ++ reflexivity.
         ++ unshelve (eapply irrValidTm, wkValidTm, Vm; eapply natValid).
            3,4: unshelve eapply validSnocℓ, ellValid;
              [..|unshelve eapply validSnocℓ, ellValid]; tea.
            tea. now eapply lrefl.
         ++ eapply evalValid, boxEvalValid, var0EllValid'.
            eapply Fwk_Fstep, Fwk_id.
         ++ etransitivity.
           -- eapply simple_app'Valid, nSuccValid, zeroValid.
              eapply castEllValid.
             ** eapply evalValid, var0EllValid'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply in_cons_ell; right; eapply ink'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply ink'.
           -- eapply evalnat_to_termValid, boxEvalValid.
             ** eapply in_cons_ell; repeat constructor.
             ** eapply Fwk_id.
             ** eapply var0EllValid'.
         ++ eapply whne_ren_wl, nem.
         ++ now etransitivity; [eapply head_ren| rewrite em].
         ++ eapply dEval'Valid, PER_Transitive.
           -- eapply xiValid.
              rewrite <- to_subst_sound.
              unshelve eapply irrValidTmRfl, (substEllSTm (G:=tNat)).
              2-6: shelve.
             ** unshelve eapply validSnocℓ, ellValid; tea.
                unshelve eapply validSnocℓ, ellValid; tea.
                now eapply lrefl.
             ** eapply boxEvalValid, var0EllValid'.
                eapply Fwk_Fstep, Fwk_id.
             ** reflexivity.
             ** rewrite <- wk_nSucc, ! wk_comp_ren_on.
                eapply (wkValidTm (A:=tNat)), nSuccValid, Vm.
           -- eapply castEllValid.
             ** eapply evalValid, var0EllValid'.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'.
                eapply in_cons_ell; right; tea.
             ** intros k' b ink'.
                eapply evalnat_to_termValid, var0EllValid'; tea.
           -- eapply evalValid, etaEllValid, var0EllValid'.
        * rewrite <- to_subst_sound with (t:= (nSucc _ _)⟨_⟩⟨_⟩), <-! to_subst_sound.
          rewrite subst_ren_subst_up, wk_subst_comp_on with (σ:= up_subst _).
          unshelve erewrite (subst_subst_eq (_ ∘r _) subst_id _ _⟨_⟩ _⟨_⟩ eq_refl), <- subst_id_on.
          { now rewrite wk_up_subst, wk1_tail, tail_scons, up_subst_id. }
          unshelve eapply irrValidTmRfl, (substEllSTm (G:=tNat)).
          2-6: shelve.
         ++ unshelve eapply validSnocℓ, ellValid; tea.
            now eapply lrefl.
         ++ eapply boxEvalValid, var0EllValid'.
            eapply Fwk_Fstep, Fwk_id.
         ++ reflexivity.
         ++ eapply (wkValidTm (A:=tNat)), nSuccValid, Vm.
    + eapply simple_app'Valid, nSuccValid, zeroValid.
      eapply evalValid, Vn.
    + eapply simple_app'Valid, nSuccValid, zeroValid.
      eapply evalValid, Vn.
  Qed.



End Xi.

















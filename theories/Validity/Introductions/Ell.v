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
    eapply redSubstValid, nodeValid.
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
      - unshelve eapply validSnocℓ, ellValid; tea.
      - shelve.
      - eapply ellValid.
      - eapply boxValid.
        * unshelve eapply evalValid, var0EllValid'.
          2: eapply ellValid.
        * intros n b inn.
          eapply evalnat_to_termValid, var0EllValid'.
          now eapply in_cons_ell.
    + eapply xiValid.
      rewrite wk_nSucc, to_subst_sound, subst_nSucc, <- to_subst_sound.
      unshelve now eapply nSuccValid, irrValidTmRfl, substEllSTm, wkValidTm; tea.
      - unshelve eapply validSnocℓ, ellValid; tea.
      - shelve.
      - eapply ellValid.
      - eapply boxValid.
        * unshelve eapply evalValid, var0EllValid'.
          2: eapply ellValid.
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
    eapply redSubstValid, irrValidTmRfl, ellElimValid.
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
    + eapply irrValidTm, xxiValid.
      erewrite ! to_subst_sound, <-! wk_Id, <-! subst_Id.
      eapply IdValid.
      - erewrite <- wk_dEval', <- subst_dEval'.
        eapply redSubstValid.
  Admitted.



End Xi.

















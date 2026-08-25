From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Tree.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application Nat Bool.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Tree.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma treeValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tTree | VΓ].
Proof.
  unshelve econstructor; intros; now eapply treeRed.
Defined.

Lemma treeValidU {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tTree : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply Wpack_return, treeTermRed.
Qed.

Lemma leafValid {Γ Γ' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tLeaf n ≅ tLeaf n' : tTree | VΓ | treeValid VΓ].
Proof.
  constructor; intros; cbn -[Wpack]; instValid Vσσ'.
  unshelve eapply leafRed; tea.
Qed.

Lemma leafValid' {Γ Γ' A A' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (VT : [Γ ||-v<l> A ≅ A' | VΓ])
  (eqA : A = tTree)
  (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tLeaf n ≅ tLeaf n' : A | VΓ | VT].
Proof.
  subst.
  constructor; intros; cbn -[Wpack]; instValid Vσσ'; eapply irrLR.
  unshelve eapply leafRed, irrLR; cycle 4; tea.
  Unshelve. tea.
Qed.

(* Lemma nodeValid' {Γ Γ' A A' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (VN : [Γ ||-v<l> A ≅ A' | VΓ])
  (eqA : A = tNat)
  (Veqn : [Γ ||-v<l> n ≅ n' : A | VΓ | VN]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : A | VΓ | VN].
Proof.
  subst.
  constructor; intros; cbn -[Wpack]; instValid Vσσ'; eapply irrLR.
  unshelve eapply succRed, irrLR; cycle 4; tea.
  Unshelve. tea.
Qed. *)

Lemma nodeValid {Γ Γ' l n n' tl tl' tr tr'} (VΓ : [||-v Γ ≅ Γ'])
  (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ])
  (Vtl : [Γ ||-v<l> tl ≅ tl' : tTree | VΓ | treeValid VΓ])
  (Vtr : [Γ ||-v<l> tr ≅ tr' : tTree | VΓ | treeValid VΓ]) :
  [Γ ||-v<l> tNode n tl tr ≅ tNode n' tl' tr' : tTree | VΓ | treeValid VΓ].
Proof.
  constructor; intros; cbn; instValid Vσσ'.
  unshelve eapply nodeRed; tea.
Qed.

Lemma nodeValid' {Γ Γ' l A A' n n' tl tl' tr tr'} (VΓ : [||-v Γ ≅ Γ'])
  (VT : [Γ ||-v<l> A ≅ A' | VΓ])
  (eqA : A = tTree)
  (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ])
  (Vtl : [Γ ||-v<l> tl ≅ tl' : tTree | VΓ | treeValid VΓ])
  (Vtr : [Γ ||-v<l> tr ≅ tr' : tTree | VΓ | treeValid VΓ]) :
  [Γ ||-v<l> tNode n tl tr ≅ tNode n' tl' tr' : A | VΓ | VT].
Proof.
  subst.
  constructor; intros; cbn -[Wpack]; instValid Vσσ'; eapply irrLR.
  unshelve eapply nodeRed; tea.
Qed.


Section TreeElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VT := treeValid (l:=l) VΓ)
    (VΓT := validSnoc VΓ VT).

  Lemma elimLeafHypTyValid {P Q}
    (VP : [Γ ,, tTree ||-v<l> P ≅ Q| VΓT]) :
    [Γ ||-v<l> elimLeafHypTy' Γ P  ≅ elimLeafHypTy' Γ Q | VΓ].
  Proof.
    unshelve eapply PiValid.
    1: eapply natValid.
    eapply substLiftS; tea.
    eapply leafValid'; [easy|].
    exact (var0Valid' _ _).
  Qed.

  Lemma elimNodeHypTyValid {P Q}
    (VP : [Γ ,, tTree ||-v<l> P ≅ Q| VΓT]) :
    [Γ ||-v<l> elimNodeHypTy' Γ P  ≅ elimNodeHypTy' Γ Q | VΓ].
  Proof.
    unshelve eapply PiValid.
    1: eapply natValid.
    unshelve eapply PiValid.
    1: eapply treeValid.
    unshelve eapply PiValid.
    1: eapply treeValid.
    eapply simpleArr'Valid.
    { rewrite !wk_comp_ren_on with (H:=Q), !wk_comp_ren_on with (H:=P).
      unshelve eapply substS, var1Valid'; [ |eapply treeValid |].
      eapply wkValidTy, VP. }
(*     rewrite 2to_subst_sound, !wk_subst_comp_on.
    eapply wkValidTy.
    replace P⟨upRen_term_term ↑⟩ with P⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩ by now bsimpl.
    replace Q⟨upRen_term_term ↑⟩ with Q⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩ by now bsimpl.
    now eapply wkValidTy.
    eassert (hupup : forall t, t⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩ = t⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩⟨wk_up (Δ:=Γ,,tNat) tTree (wk1 tTree)⟩) by (intros; now bsimpl). *)
    eapply simpleArr'Valid.
    { rewrite !wk_comp_ren_on with (H:=Q), !wk_comp_ren_on with (H:=P).
      unshelve eapply substS, var0Valid'; [ |eapply treeValid |].
      eapply wkValidTy, VP. }
    eapply substS, nodeValid.
    { rewrite !wk_comp_ren_on with (H:=Q), !wk_comp_ren_on with (H:=P).
      eapply wkValidTy, VP. }
    + eapply varnValid.
      eapply in_there' with (A:=tNat), in_there' with (A:=tNat), in_here'.
    + eapply varnValid.
      eapply in_there' with (A:=tTree), in_here'.
    + eapply varnValid.
      constructor.
  Qed.

  Lemma treeElimCongValid {P P' hl hl' hn hn'}
    (VP : [Γ ,, tTree ||-v<l> P ≅ P' | VΓT ])
    (Vhl : [Γ ||-v<l> hl ≅ hl' : _ | VΓ | elimLeafHypTyValid VP ])
    (Vhn : [Γ ||-v<l> hn ≅ hn' : _ | VΓ | elimNodeHypTyValid VP])
    {t t'}
    (Vt : [Γ ||-v<l> t ≅ t' : tTree | VΓ | VT])
    (VPt := substS VP Vt)
    : [Γ ||-v<l> tTreeElim P hl hn t ≅ tTreeElim P' hl' hn' t' : _ | VΓ | VPt].
  Proof.
    pose proof (elimLeafHypTyValid VP).
    pose proof (elimNodeHypTyValid VP).
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VT Vσσ').
    instValid Vuσ.
    change (tTreeElim ?P ?hl ?hn ?t)[?σ] with (tTreeElim P[up_subst σ] hl[σ] hn[σ] t[σ]).
    eapply irrLREq. 1: now rewrite subst_ren_subst_up.
    unshelve eapply treeElimRedEq; tea.
    4-6: now escape.
    + clear dependent t; clear dependent t'; intros Ξ wfΞ ρΞ ???.
      rewrite 2subst_ren_wk, 2to_subst_sound, 2subst_comp_on, 2eq_upwk.
      unshelve (eapply validTyExt; tea); tea.
      unshelve eapply consWkSubst; tea.
      eapply irrLR, Rt.
    + now erewrite 2!subst_elimLeafHypTy'.
    + now erewrite 2!subst_elimNodeHypTy'.
    + eapply irrLREq; tea; now erewrite subst_elimLeafHypTy'.
    + eapply irrLREq; tea; now erewrite subst_elimNodeHypTy'.
  Qed.
End TreeElimValid.

Lemma treeElimValid {Γ Γ' l P hl hl' hn hn' t t'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VT := treeValid (l:=l) VΓ)
    (VΓT := validSnoc VΓ VT)
    (VP : [Γ ,, tTree ||-v<l> P | VΓT])
    (Vhl : [Γ ||-v<l> hl ≅ hl' : _ | VΓ | elimLeafHypTyValid VΓ VP])
    (Vhn : [Γ ||-v<l> hn ≅ hn' : _ | VΓ | elimNodeHypTyValid VΓ VP])
    (Vt : [Γ ||-v<l> t ≅ t' : _ | VΓ | VT])
    (VPt := substS VP Vt):
    [Γ ||-v<l> tTreeElim P hl hn t : _ | VΓ | VPt].
Proof. now eapply lrefl, treeElimCongValid. Qed.

Section TreeElimRedValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VT := treeValid (l:=l) VΓ)
    (VΓT := validSnoc VΓ VT)
    { P P' hl hl' hn hn'}
    (VP : [Γ ,, tTree ||-v<l> P ≅ P' | VΓT ])
    (Vhl : [Γ ||-v<l> hl ≅ hl' : _ | VΓ | elimLeafHypTyValid VΓ VP])
    (Vhn : [Γ ||-v<l> hn ≅ hn' : _ | VΓ | elimNodeHypTyValid VΓ VP]).

  Lemma treeElimLeafValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN])
    (VPLn := substS VP (leafValid _ Vn)) :
    [Γ ||-v<l> tTreeElim P hl hn (tLeaf n) ≅ tApp hl n : _ | VΓ | VPLn].
  Proof.
    eapply redSubstValid.
    * constructor; intros; rewrite subst_ren_subst_up.
      instValid Vσσ'; instValid (liftSubst' VT Vσσ'); escape.
      rewrite <- subst_app.
      change (tTreeElim ?P ?hl ?hn ?t)[?σ] with (tTreeElim P[up_subst σ] hl[σ] hn[σ] t[σ]).
      change (tLeaf ?n)[?σ] with (tLeaf n[σ]).
      eapply redtm_treeElimLeaf; tea; refold.
      + now erewrite subst_elimLeafHypTy'.
      + now erewrite subst_elimNodeHypTy'.
    * eapply lrefl, appcongValid'; tea.
      1: unshelve (eapply irrValidTm; tea; now eapply natValid); tea; now eapply lrefl.
      rewrite to_subst_sound with (σ:=n..), subst_ren_subst_up. f_equal.
      rewrite <- up_to_subst, <- to_subst_sound. rewrite up_wk1_ren_on. now bsimpl.
  Qed.

  Lemma substSΠ' { F F' G G' t u}
    {VF : [Γ ||-v< l > F ≅ F' |VΓ]}
    (VΠ : [Γ ||-v<l> tProd F G ≅ tProd F' G' | VΓ])
    (Vt : [Γ ||-v<l> t ≅ u : F | VΓ |VF]) :
    [_ ||-v<l> G[t..] ≅ G'[u..] | VΓ].
  Proof.
    unshelve eapply substSΠ, irrValidTm, Vt.
    3: eapply VΠ.
    3: eapply lrefl, irrValidTy, VF.
    all: now eapply lrefl.
  Qed.

  Lemma treeElimNodeValid {n tl tr}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN])
    (Vtl : [Γ ||-v<l> tl : tTree | VΓ | VT])
    (Vtr : [Γ ||-v<l> tr : tTree | VΓ | VT])
    (VPnode := substS VP (nodeValid _ Vn Vtl Vtr)) :
    [Γ ||-v<l> tTreeElim P hl hn (tNode n tl tr) ≅
      tApp (tApp (tApp (tApp (tApp hn n) tl) tr) (tTreeElim P hl hn tl)) (tTreeElim P hl hn tr) :
       _ | VΓ | VPnode].
  Proof.
    eapply redSubstValid.
    * constructor; intros; rewrite subst_ren_subst_up.
      instValid Vσσ'; instValid (liftSubst' VT Vσσ'); escape.
      rewrite <-! subst_app.
      change (tTreeElim ?P ?hl ?hn ?t)[?σ] with (tTreeElim P[up_subst σ] hl[σ] hn[σ] t[σ]).
      change (tNode ?n ?tl ?tr)[?σ] with (tNode n[σ] tl[σ] tr[σ]).
      eapply redtm_treeElimNode; tea; refold.
      + now erewrite subst_elimLeafHypTy'.
      + now erewrite subst_elimNodeHypTy'.
    * epose proof (VPn := substSΠ' (elimNodeHypTyValid VΓ VP) Vn).
      rewrite 4 Extra.subst_prod in VPn.
      epose proof (VPtl := substSΠ' VPn Vtl).
      rewrite 2 Extra.subst_prod in VPtl.
      epose proof (VPtr := substSΠ' VPtl Vtr).
      eapply lrefl, simple_app'Valid.
      2: now unshelve now eapply treeElimCongValid.
      eapply simple_app'Valid.
      2: now unshelve now eapply treeElimCongValid.
      eapply appcongValid'; [|shelve..].
      eapply appcongValid'; [|shelve..].
      now eapply appcongValid'; [|shelve..].
      Unshelve.
      21: now rewrite Extra.subst_prod.
      16: now rewrite 2 Extra.subst_prod.
      8:{ now rewrite <- elimNodeHypTyCod_subst_terms,
            elimNodeHypTyCod_subst_terms_aux. }
      14:{ (unshelve now eapply irrValidTm, Vn; eapply natValid); tea; now eapply lrefl. }
      12:{ (unshelve now eapply irrValidTm, Vtl; eapply treeValid); tea; now eapply lrefl. }
      7:{ (unshelve now eapply irrValidTm, Vtr; eapply treeValid); tea; now eapply lrefl. }
      8: eapply VPn.
      5: eapply VPtl.
      2: eapply simpleArr'Valid, simpleArr'Valid, VPnode; eapply substS; tea.
      1: eapply simpleArr'Valid, VPnode; eapply substS; tea.
  Qed.


End TreeElimRedValid.

  Lemma dEval'Valid {Γ Γ' d d' n n' l} (VΓ : [||-v Γ ≅ Γ']) :
    [Γ ||-v< l > d ≅ d' : _ | _ | treeValid VΓ] ->
    [Γ ||-v< l > n ≅ n' : _ | _ | simpleArr'Valid VΓ (natValid _) (boolValid _)] ->
    [Γ ||-v< l > dEval' Γ d n ≅ dEval' Γ d' n' : _ | _ | natValid VΓ].
  Proof.
    intros Vd Vn.
    assert (VΓN : [||-v Γ,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [ | easy..]).
    assert (VΓNT : [||-v Γ,, tNat,, tTree ≅ _])
      by (unshelve eapply validSnoc, treeValid; [|easy..]).
    assert (VΓNTT : [||-v Γ,, tNat,, tTree,, tTree ≅ _])
      by (unshelve eapply validSnoc, treeValid; [ | easy..]).
    assert (VΓNTTN : [||-v Γ,, tNat,, tTree,, tTree,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [ | easy..]).
    assert (VΓNTTNN : [||-v Γ,, tNat,, tTree,, tTree,, tNat,, tNat ≅ _])
      by (unshelve eapply validSnoc, natValid; [ | easy..]).
    unfold dEval'.
    unshelve eapply irrValidTmRfl, treeElimCongValid; tea.
    + eapply natValid.
    + reflexivity.
    + unshelve (now eapply irrValidTmRfl, Lambda.lamCongValid, var0Valid); tea.
      eapply natValid.
    + unfold dEvalNode'.
      unshelve (eapply irrValidTmRfl; [..| do 5 eapply Lambda.lamCongValid]).
      - eapply VΓ.
      - eapply natValid.
      - eapply treeValid.
      - eapply treeValid.
      - eapply natValid.
      - shelve.
      - shelve.
      - eapply natValid.
      - eapply natValid.
      - reflexivity.
      - unshelve eapply irrValidTmRfl, boolElimCongValid; tea.
        * eapply natValid.
        * unshelve eapply (simple_app'Valid _ (VF:=natValid _)), varnValid.
         ++ eapply simpleArr'Valid, boolValid.
            eapply natValid.
         ++ unshelve now eapply irrValidTmRfl, wkValidTm, wkValidTm, wkValidTm, wkValidTm, wkValidTm, Vn; tea.
            1,3,5,7,9 : tea. Unshelve.
         ++ do 4 eapply in_there' with (A:=tNat).
            eapply in_here'.
        * reflexivity.
        * eapply varnValid.
          eapply in_there' with (A:=tNat), in_here'.
        * eapply varnValid.
          eapply in_here'.
  Qed.

End Tree.

From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Tree.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application Nat.

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
    [Γ ||-v<l> elimLeafHypTy P  ≅ elimLeafHypTy Q | VΓ].
  Proof.
    unfold elimLeafHypTy.
    unshelve eapply PiValid.
    1: eapply natValid.
    eapply substLiftS; tea. cbn.
    eapply leafValid'; [easy|].
    change tNat with tNat⟨↑⟩.
    eapply var0Valid'.
  Qed.

  Lemma elimNodeHypTyValid {P Q}
    (VP : [Γ ,, tTree ||-v<l> P ≅ Q| VΓT]) :
    [Γ ||-v<l> elimNodeHypTy P  ≅ elimNodeHypTy Q | VΓ].
  Proof.
    unfold elimNodeHypTy.
    unshelve eapply PiValid.
    1: eapply natValid.
    unshelve eapply PiValid.
    1: eapply treeValid.
    unshelve eapply PiValid.
    1: eapply treeValid.
    eapply simpleArrValid.
    erewrite <- 2wk1_ren_on.
    eapply wkValidTy.
    replace P⟨upRen_term_term ↑⟩ with P⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩ by now bsimpl.
    replace Q⟨upRen_term_term ↑⟩ with Q⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩ by now bsimpl.
    now eapply wkValidTy.
    eassert (hupup : forall t, t⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩ = t⟨wk_up (Δ:=Γ) tTree (wk1 tNat)⟩⟨wk_up (Δ:=Γ,,tNat) tTree (wk1 tTree)⟩) by (intros; now bsimpl).
    eapply simpleArrValid.
    rewrite 2 hupup.
    now do 2 eapply wkValidTy.
    eapply substLiftS.
    rewrite 2 hupup.
    now do 2 eapply wkValidTy.
    eapply nodeValid'; [easy|..].
    + eapply varnValid.
      change tNat with tNat⟨↑⟩⟨↑⟩.
      repeat constructor.
    + eapply varnValid.
      change tTree with tTree⟨↑⟩.
      repeat constructor.
    + eapply varnValid.
      constructor.
    Unshelve.
    2,4,8: unshelve eapply validSnoc, treeValid.
    3,6,9: unshelve eapply validSnoc, natValid.
    14: unshelve eapply treeValid.
    all: tea.
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
    instValid Vuσ; cbn -[elimLeafHypTy elimLeafHypTyValid elimNodeHypTy elimNodeHypTyValid Wpack] in *.
    eapply irrLREq. 1: now rewrite singleSubstComm'.
    unshelve eapply treeElimRedEq; tea.
    4-6: now escape.
    + clear dependent t; clear dependent t'; intros Ξ wfΞ ρΞ ???.
      rewrite 2eq_upren', 2!up_single_subst; eapply validTyExt; tea.
      unshelve eapply wkSubst in Vσσ' as VρΞ; tea.
      now unshelve econstructor.
    + now rewrite 2!elimLeafHypTy_subst.
    + now rewrite 2!elimNodeHypTy_subst.
    + eapply irrLREq; tea; now rewrite elimLeafHypTy_subst.
    + eapply irrLREq; tea; now rewrite elimNodeHypTy_subst.
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
    * constructor; intros; rewrite singleSubstComm'.
      instValid Vσσ'; instValid (liftSubst' VT Vσσ'); escape.
      eapply redtm_treeElimLeaf; tea; refold.
      + now rewrite elimLeafHypTy_subst.
      + now rewrite elimNodeHypTy_subst.
    * eapply lrefl, appcongValid'.
      1: eapply Vhl.
      2: now bsimpl.
      unshelve eapply irrValidTm, Vn; tea.
      2: eapply irrValidTy; tea.
      all: now eapply lrefl.
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
    * constructor; intros; rewrite singleSubstComm'.
      instValid Vσσ'; instValid (liftSubst' VT Vσσ'); escape.
      eapply redtm_treeElimNode; tea; refold.
      + now rewrite elimLeafHypTy_subst.
      + now rewrite elimNodeHypTy_subst.
    * epose proof (VPn := substSΠ' (elimNodeHypTyValid VΓ VP) Vn); cbn in VPn.
      epose proof (VPtl := substSΠ' VPn Vtl); cbn in VPtl.
      epose proof (VPtr := substSΠ' VPtl Vtr); cbn in VPtr.
      eapply lrefl, simple_appValid.
      2: now unshelve now eapply treeElimCongValid.
      eapply simple_appValid.
      2: now unshelve now eapply treeElimCongValid.
      eapply appcongValid'; [|shelve..].
      eapply appcongValid'; [|shelve..].
      now eapply appcongValid'; [|shelve..].
      Unshelve.
      21: reflexivity.
      16: reflexivity. all: refold.
      8:{ cbn. f_equal; [|f_equal].
          + now rewrite 2shift_up_eq, shift_one_eq, up_shift_one_eq.
          + now rewrite 3shift_up_eq, up_shift_up_eq, 2up_shift_one_eq.
          + rewrite 2shift_upRen_eq, 6shift_up_eq, liftSubst_can, 3singleSubstComm', 3up_shift_up_eq, 3 up_shift_one_eq.
            do 4 f_equal. cbn.
            now rewrite shift_up_eq, 3shift_one_eq. }
      cbn in *.
      14:{ (unshelve now eapply irrValidTm, Vn; eapply natValid); tea; now eapply lrefl. }
      12:{ (unshelve now eapply irrValidTm, Vtl; eapply treeValid); tea; now eapply lrefl. }
      7:{ (unshelve now eapply irrValidTm, Vtr; eapply treeValid); tea; now eapply lrefl. }
      8: eapply VPn.
      5: eapply VPtl.
      2: eapply simpleArrValid, simpleArrValid, VPnode; eapply substS; tea.
      1: eapply simpleArrValid, VPnode; eapply substS; tea.
  Qed.


End TreeElimRedValid.

End Tree.

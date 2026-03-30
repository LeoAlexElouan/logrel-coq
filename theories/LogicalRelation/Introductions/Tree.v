
From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Nat.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Tree.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma treeRedTy {Γ} : [|- Γ] -> [Γ ||-Tree tTree ≅ tTree].
Proof.
  constructor; eapply redtywf_refl; gen_typing.
Qed.

Definition StreeRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-S<l> tTree] :=
  LRTree_ l (treeRedTy wfΓ).

Definition treeRed {Γ l} (wfΓ : [|- Γ]) : [Γ ||-<l> tTree] :=
  WAd_return (StreeRed wfΓ).


Lemma treeURedTm {Δ} (wfΔ : [|-Δ]) : URedTm zero Δ tTree.
Proof.
  exists tTree; [| constructor].
  eapply redtmwf_refl; gen_typing.
Defined.

Lemma treeTermRed {Δ} (wfΔ : [|-Δ]) : [Δ ||-<one> tTree : U | LRU_ (redUOneCtx wfΔ)].
Proof.
  unshelve econstructor; try now eapply treeURedTm.
  1: cbn; gtyping.
  eapply redTyRecBwd; now eapply StreeRed.
Defined.

Lemma SleafRed {Γ l A A' B B' n n'} {NN : [Γ ||-Nat A ≅ A' ]} {NT : [Γ ||-Tree B ≅ B']} : [Γ ||-<l> n ≅ n' : _ | LRNat_ l NN] ->
  [Γ ||-S<l> tLeaf n ≅ tLeaf n' : _ | LRTree_ l NT].
Proof.
  assert [|-Γ] by (pose (LRTree_ l NT); escape; gtyping).
  intros Rn. inversion Rn; subst. escape.
  eapply (Build_TreeRedTmEq (tLeaf n) (tLeaf n')).
  1,2: eapply redtmwf_refl; eapply ty_leaf; gen_typing.
  + destruct redL, redR.
    eapply convtm_leaf; eapply convtm_exp; tea;
    [eapply wft_term|eapply convty_term]; gtyping.
  + now constructor.
Defined.

Lemma leafRed {Γ l n n'} (wfΓ : [|-Γ]) :
  [Γ ||-< l > n ≅ n' : _ | natRed (l:=l) wfΓ] ->
  [Γ ||-< l > tLeaf n ≅ tLeaf n' : _ | treeRed (l:=l) wfΓ].
Proof.
  intros Rn.
  eapply (dSplit_bind_return Rn).
  intros ??? onatRed oRn oir. cbn.
  unshelve now eapply SirrLR, SleafRed, SirrLR, Rn.
  4: eapply natRedTy.
  4: eapply treeRedTy.
  all: tea.
Defined.

Lemma SnodeRed {Γ l A A' B B' n n' tl tl' tr tr'}
  {NN : [Γ ||-Nat A ≅ A']} {NT : [Γ ||-Tree B ≅ B']} :
  [Γ ||-S<l> n ≅ n' : _ |LRNat_ l NN] ->
  [Γ ||-S<l> tl ≅ tl' : _ |LRTree_ l NT] ->
  [Γ ||-S<l> tr ≅ tr' : _ |LRTree_ l NT] ->
  [Γ ||-S<l> tNode n tl tr ≅ tNode n' tl' tr' : _ |LRTree_ l NT].
Proof.
  assert [|-Γ] by (pose (LRTree_ l NT); escape; gtyping).
  intros Rn Rtl Rtr; inversion Rn; inversion Rtl; inversion Rtr; subst.
  escape; econstructor.
  1,2: eapply redtmwf_refl; eapply ty_node; gen_typing.
  + destruct redL, redR, redL0, redR0, redL1, redR1.
    eapply convtm_node; eapply convtm_exp; tea;
    first [eapply wft_term| eapply convty_term]; gtyping.
  + now constructor.
Defined.

Lemma nodeRed {Γ l n n' tl tl' tr tr'} (wfΓ : [|-Γ]) :
  [Γ ||-< l > n ≅ n' : _ | natRed (l:=l) wfΓ] ->
  [Γ ||-< l > tl ≅ tl' : _ | treeRed (l:=l) wfΓ] ->
  [Γ ||-< l > tr ≅ tr' : _ | treeRed (l:=l) wfΓ] ->
  [Γ ||-< l > tNode n tl tr ≅ tNode n' tl' tr' : _ | treeRed (l:=l) wfΓ].
Proof.
  intros Rn Rtl Rtr.
  eapply (dSplit_bind Rn).
  intros ??? onatRed oRn.
  unshelve eapply Wpackrefold; tea.
  eapply (Split_wk_bind Rtl wfΔ ρ).
  intros ??? oRtl.
  unshelve eapply Wpackrefold; tea.
  eapply (dSplit_wk_bind_return Rtr wfΞ (ρΞ ∘w ρ)).
  intros Ω wfΩ ρΩ otree oRtr oirr.
  rewrite 4 wk_comp_ren_on.
  unshelve eapply SirrLR, SnodeRed; refold.
  5: now eapply natRedTy.
  3: now eapply treeRedTy.
  tea.
  + unshelve eapply SirrLR, Rn; tea.
    1,2: now eapply overtree_PSh.
  + unshelve eapply SirrLR, Rtl; tea;
      rewrite wk_comp_assoc; tea.
    now eapply overtree_PSh.
  + unshelve eapply SirrLR, Rtr; tea;
      rewrite wk_comp_assoc; tea.
Qed.

Lemma elimLeafHypTy_subst {Γ Δ P} (σ : substitution) :
  elimLeafHypTy' Γ P[up_subst σ] = (elimLeafHypTy' Δ P)[σ].
Proof.
  rewrite <- subst_prod. f_equal.
  rewrite subst_ren_subst_up. f_equal.
  rewrite 2up_wk1_ren_on. now bsimpl.
Qed.


(* Lemma liftSubst_can {t u} : t[u]⇑ = t⟨upRen_term_term ↑⟩[u..].
Proof.
  rewrite <- up_single_subst.
  f_equal.
  rewrite rinstInst'_term.
  now bsimpl.
Qed. *)

(* Lemma up_shift_up_eq t σ : t⟨upRen_term_term ↑⟩[up_term_term (up_term_term σ)] = t[up_term_term σ]⟨upRen_term_term ↑⟩.
Proof.
  now bsimpl.
Qed.

Lemma up_shift_one_eq t a : t⟨upRen_term_term ↑⟩[up_term_term a..] = t.
Proof.
  now bsimpl.
Qed. *)

Lemma elimNodeHypTy_subst {Γ Δ P} σ :
  elimNodeHypTy' Δ P[up_subst σ] = (elimNodeHypTy' Γ P)[σ].
Proof.
  rewrite <- 3subst_prod. f_equal. f_equal. f_equal.
  erewrite <- 2subst_arr'. f_equal.
  { erewrite <- subst_up_wk1. f_equal.
    rewrite up_wk1_ren_on. now bsimpl. }
  erewrite <- subst_up_wk1. rewrite 2wk1_ren_on. f_equal.
  f_equal.
  { rewrite !up_wk1_ren_on. now bsimpl. }
  rewrite 2wk1_ren_on. f_equal.
  rewrite subst_ren_subst_up. f_equal.
  rewrite !up_wk1_ren_on. now bsimpl.
  Unshelve. all: tea.
Qed.
(* 
Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed. *)

Section STreeElimRedEq.
  Context {Γ l P Q hl hl' hn hn'}
    (NT : [Γ ||-Tree tTree ≅ tTree])
    (RT := LRTree_ _ NT)
    (WtP : [Γ ,, tTree |- P])
    (WtQ : [Γ ,, tTree |- Q])
    (eqPQ : [Γ,, tTree |- P ≅ Q])
    (RPQext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RT]),
      [Γ ||-<l> P[n..] ≅ Q[n'..]])
    (RPQl : [Γ ||-<l> elimLeafHypTy' Γ P ≅ elimLeafHypTy' Γ Q])
    (Rhl : [Γ ||-<l> hl ≅ hl' : _ | RPQl])
    (RPQn : [Γ ||-<l> elimNodeHypTy' Γ P ≅ elimNodeHypTy' Γ Q])
    (Rhn : [Γ ||-<l> hn ≅ hn' : _ | RPQn ]) .

  Let RPext : forall n n' (Rn : [Γ ||-S<l> n ≅ n' : _ | RT]),
      [Γ ||-<l> P[n..] ≅ P[n'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.

(*   Lemma redΠcod Γ F F' G G'  *)

  Lemma StreeElimRedEq :
    (forall t t' (Rt : [Γ ||-S<l> t ≅ t' : _ | RT]),
      [Γ ||-<l> tTreeElim P hl hn t ≅ tTreeElim Q hl' hn' t' : _ |  (RPQext _ _ Rt) ]).
  Proof.
    eassert ([|-Γ]) as wfΓ by (escape; gtyping).
    intros t t' Rt.
    set (RP := RPQext t t' Rt); clearbody RP.
    induction Rt as [ ??????? prop ih| | ??????? Rtl ihl Rtr ihr| ].
    - set (Rtu := Build_TreeRedTmEq _ _ redL redR eq prop : [Γ ||-S<l> t ≅ u : _ | RT]).
      pose proof (redTmFwd' Rtu) as []; eapply redSubstTmEq.
      + unshelve eapply irrLRConv, ih;
        first [eapply RPQext | eapply RPext]; tea; now symmetry.
      + escape; eapply redtm_treeelim; tea; gen_typing.
      + escape; eapply redtm_treeelim; tea; [..| gtyping].
        1,2: now eapply ty_conv.
    - change [Γ ||-S<l> n ≅ n' : _ | LRNat_ l (natRedTy wfΓ)] in Rn.
      intros; eapply redSubstTmEq; cycle 1.
      + escape; eapply redtm_treeElimLeaf; tea.
      + escape; eapply redtm_treeElimLeaf; tea.
        1,2: now eapply ty_conv.
      + eapply Wpack_return in Rn as WRn.
        eassert (Hcod : forall P n, P⟨wk_up tTree (wk1 tNat)⟩[(tLeaf (tRel 0))..][n..] = P[(tLeaf n)..]).
        { clear dependent P. clear dependent n. intros.
          rewrite to_subst_sound, subst_ren_subst_up. f_equal.
          rewrite up_wk1_ren_on, <- up_to_subst, <- to_subst_sound. now bsimpl. }
        eapply irrLREq, appcongTerm, WRn.
        2: eapply Rhl.
        eapply Hcod.
        Unshelve.
        now rewrite 2Hcod.
    - change [Γ ||-S<l> n ≅ n' : _ | LRNat_ l (natRedTy wfΓ)] in Rn.
      change [Γ ||-S<l> tl ≅ tl' : _ | RT] in Rtl.
      change [Γ ||-S<l> tr ≅ tr' : _ | RT] in Rtr.
      intros; eapply redSubstTmEq; cycle 1.
      + escape; eapply redtm_treeElimNode; tea.
      + escape; eapply redtm_treeElimNode; tea.
        1,2: now eapply ty_conv.
      + unshelve eapply simple_appcongTerm, ihr.
        1: now eapply RPQext.
        1: now eapply ArrRedTy; eapply RPQext; [..| eapply (SnodeRed (NN:=natRedTy wfΓ))].
        unshelve eapply simple_appcongTerm, ihl.
        1: now eapply RPQext.
        1: now eapply ArrRedTy, ArrRedTy; eapply RPQext; [..| eapply (SnodeRed (NN:=natRedTy wfΓ))].
        eapply Wpack_return in Rn as WRn.
        eapply Wpack_return in Rtl as WRtl.
        eapply Wpack_return in Rtr as WRtr.
        epose proof (codSubst RPQn WRn) as RPQnn; cbn in RPQnn.
        epose proof (codSubst RPQnn WRtl) as RPQnntl; cbn in RPQnntl.
        epose proof (codSubst RPQnntl WRtr) as RPQnntltr; cbn in RPQnntltr.
        eapply irrLREq, appcongTerm, WRtr; [shelve|..].
        eapply irrLREq, appcongTerm, WRtl;  [shelve|..].
        eapply irrLREq, appcongTerm, WRn;  [shelve|..].
        eapply Rhn. Unshelve.
        12: cbn; reflexivity.
        9: cbn; reflexivity.
        4:{ cbn; f_equal; [|f_equal].
          * rewrite 2 shift_up_eq.
            now rewrite 2 shift_up_eq, shift_one_eq, up_shift_one_eq.
          * now rewrite 3 shift_up_eq, up_shift_up_eq, 2 up_shift_one_eq.
          * rewrite 2 shift_upRen_eq, 6 shift_up_eq, liftSubst_can, 3 singleSubstComm'.
            rewrite 3 up_shift_up_eq, 3 up_shift_one_eq.
            do 4 f_equal. cbn.
            now rewrite shift_up_eq, 3 shift_one_eq. }
        6,7: eapply RPQnn.
        3,4: eapply RPQnntl.
        1: eapply RPQnntltr.
    - epose proof (SneNfTermEq RT r).
      escape.
      eapply irrLR.
      eapply neNfTermEq; constructor.
      + now eapply ty_treeElim.
      + eapply ty_conv.
        eapply ty_treeElim; tea.
        * now eapply ty_conv.
        * now eapply ty_conv.
        * now symmetry.
      + destruct r; now eapply convneu_treeElim.
      Unshelve.
      2: now eapply lrefl.
  Qed.

End STreeElimRedEq.

Section TreeElimRedEq.
  Context {Γ l P Q}
    (wfΓ : [|- Γ])
    (WtP : [Γ ,, tTree |- P])
    (WtQ : [Γ ,, tTree |- Q])
    (eqPQ : [Γ,, tTree |- P ≅ Q])
    (RPQext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) t t' (Rt : [Δ ||-<l> t ≅ t' : _ | treeRed (l:=l) wfΔ ]),
      [Δ ||-<l> P⟨wk_up tTree ρ⟩[t..] ≅ Q⟨wk_up tTree ρ⟩[t'..]]).


  Let RPQextnow : forall t t',
    [Γ ||-<l> t ≅ t' : _ | treeRed (Γ := Γ) (l:=l) wfΓ] -> [Γ ||-<l> P[t..] ≅ Q[t'..]].
  Proof.
    intros t t' Rtt'.
    epose (RPQ := RPQext Γ wfΓ wk_id t t' Rtt').
    replace P with P⟨wk_id (Γ:=Γ,,tTree)⟩ by eapply wk_id_ren_on.
    now replace Q with Q⟨wk_id (Γ:=Γ,,tTree)⟩ by eapply wk_id_ren_on.
  Qed.

  Context {hl hl' hn hn'}
    (RPQl : [Γ ||-<l> elimLeafHypTy P ≅ elimLeafHypTy Q])
    (Rhl : [Γ ||-<l> hl ≅ hl' : _ | RPQl ])
    (RPQn : [Γ ||-<l> elimNodeHypTy P ≅ elimNodeHypTy Q])
    (Rhn : [Γ ||-<l> hn ≅ hn' : _ | RPQn ]).

  Let RPext : forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) t t' (Rn : [Δ ||-<l> t ≅ t' : _ | treeRed (l:=l) wfΔ]),
      [Δ ||-<l> P⟨wk_up tTree ρ⟩[t..] ≅ P⟨wk_up tTree ρ⟩[t'..]].
  Proof.
    intros; etransitivity; [|symmetry];  eapply RPQext; tea; now eapply urefl.
  Qed.


  Lemma treeElimRedEq t t' (Rt : [Γ ||-<l> t ≅ t' : _ | treeRed wfΓ]):
      [Γ ||-<l> tTreeElim P hl hn t ≅ tTreeElim Q hl' hn' t' : _ | RPQextnow _ _ Rt].
  Proof.
    eapply (dSplit_bind Rt).
    intros Δ wfΔ ρ oRT oRt.
    eapply Wpackrefold.
    eassert [|-Δ,,tTree] as wfΔT by (eapply wfc_cons; gtyping).
    rewrite <- 2wk_treeElim.
    eapply irrLREq, StreeElimRedEq; refold.
    1: symmetry; eapply subst_ren_wk_up.
    Unshelve.
    + now eapply wft_wk.
    + now eapply wft_wk.
    + now eapply convty_wk.
    + unshelve eapply irrLREq, wkLRTm, Rhl; tea.
      symmetry; eapply wk_elimLeafHypTy.
    + unshelve eapply irrLREq, wkLRTm, Rhn; tea.
      symmetry; eapply wk_elimNodeHypTy.
    + easy.
    + now eapply treeRedTy.
    + clear dependent t; clear t'; intros t t' Rt.
      eapply (RPQext _ wfΔ), Wpack_return, SirrLR, Rt.
    + now unshelve now eapply SirrLREq, Rt.
    + rewrite 2 wk_elimLeafHypTy.
      now eapply wkLRTy.
    + rewrite 2 wk_elimNodeHypTy.
      now eapply wkLRTy.
  Qed.

End TreeElimRedEq.

End Tree.
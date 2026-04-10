From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Nat.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Nat.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma natValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tNat | VΓ].
Proof.
  unshelve econstructor; intros; now eapply natRed.
Defined.

Lemma natValidU {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tNat : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply Wpack_return, natTermRed.
Qed.

Lemma zeroValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']):
  [Γ ||-v<l> tZero : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply zeroRed; tea.
Qed.

Lemma succValid' {Γ Γ' A A' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (VN : [Γ ||-v<l> A ≅ A' | VΓ])
  (eqA : A = tNat)
  (Veqn : [Γ ||-v<l> n ≅ n' : A | VΓ | VN]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : A | VΓ | VN].
Proof.
  subst.
  constructor; intros; cbn -[Wpack]; instValid Vσσ'; eapply irrLR.
  unshelve eapply succRed, irrLR; cycle 4; tea.
  Unshelve. tea.
Qed.

Lemma succValid {Γ Γ' l n n'} (VΓ : [||-v Γ ≅ Γ'])
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]) :
  [Γ ||-v<l> tSucc n ≅ tSucc n' : tNat | VΓ | natValid VΓ].
Proof.
  constructor; intros; cbn; instValid Vσσ'.
  unshelve eapply succRed; cycle 3; first [eapply natRedTy| tea].
Qed.


Section NatElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN).

  Lemma elimSuccHypTyValid {P Q}
    (VP : [Γ ,, tNat ||-v<l> P ≅ Q| VΓN]) :
    [Γ ||-v<l> elimSuccHypTy' Γ P  ≅ elimSuccHypTy' Γ Q | VΓ].
  Proof.
    unshelve eapply PiValid.
    1: exact VN.
    eapply simpleArr'Valid; tea.
    eapply substLiftS; tea.
    now eapply succValid', var0Valid.
  Qed.

  Lemma natElimCongValid {P P' hz hz' hs hs'}
    (VP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN ])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VP])
    {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : _ | VΓ | VPn].
  Proof.
    pose proof (elimSuccHypTyValid VP).
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VN Vσσ').
    instValid Vuσ.
    change (tNatElim ?P ?hz ?hs ?n)[?σ] with (tNatElim P[up_subst σ] hz[σ] hs[σ] n[σ]).
    eapply irrLREq. 1: now rewrite subst_ren_subst_up.
    unshelve eapply natElimRedEq; tea.
    3-5: now escape.
    + clear dependent n; clear dependent n'; intros Ξ wfΞ ρΞ ???.
      rewrite 2subst_ren_wk, 2to_subst_sound, 2subst_comp_on, 2eq_upwk.
      unshelve (eapply validTyExt; tea); tea.
      unshelve eapply consWkSubst; tea.
      eapply irrLR, Rn.
    + now erewrite 2!subst_elimSuccHypTy'.
    + eapply irrLREq; tea; now rewrite subst_ren_subst_up.
    + eapply irrLREq; tea; now erewrite subst_elimSuccHypTy'.
  Qed.
End NatElimValid.

Lemma natElimValid {Γ Γ' l P hz hz' hs hs' n n'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tNat ||-v<l> P | VΓN])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tNatElim P hz hs n : _ | VΓ | VPn].
Proof. now eapply lrefl, natElimCongValid. Qed.

Section NatElimRedValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := natValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' hz hz' hs hs'}
    (VP : [Γ ,, tNat ||-v<l> P ≅ P' | VΓN ])
    (VPz := substS VP (zeroValid VΓ))
    (Vhz : [Γ ||-v<l> hz ≅ hz' : P[tZero..] | VΓ | VPz])
    (Vhs : [Γ ||-v<l> hs ≅ hs' : _ | VΓ | elimSuccHypTyValid VΓ VP]).

  Lemma natElimZeroValid  :
    [Γ ||-v<l> tNatElim P hz hs tZero ≅ hz : _ | VΓ | VPz].
  Proof.
    eapply redSubstValid. 2: now eapply lrefl.
    constructor; intros.
    change (tNatElim ?P ?hz ?hs ?n)[?σ] with (tNatElim P[up_subst σ] hz[σ] hs[σ] n[σ]).
    rewrite subst_ren_subst_up.
    instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
    eapply redtm_natElimZero; tea.
    + now rewrite <- (subst_ren_subst_up _ tZero σ).
    + now erewrite subst_elimSuccHypTy'.
  Qed.

  Lemma natElimSuccValid {n}
    (Vn : [Γ ||-v<l> n : tNat | VΓ | VN])
    (VPSn := substS VP (succValid _ Vn)) :
    [Γ ||-v<l> tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : _ | VΓ | VPSn].
  Proof.
    eapply redSubstValid.
    * constructor; intros; rewrite subst_ren_subst_up.
      instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
      rewrite <-2 subst_app.
      change (tNatElim ?P ?hz ?hs ?n)[?σ] with (tNatElim P[up_subst σ] hz[σ] hs[σ] n[σ]).
      change (tSucc ?n)[?σ] with (tSucc n[σ]).
      eapply redtm_natElimSucc; tea; refold.
      + now rewrite <- (subst_ren_subst_up _ tZero σ).
      + now erewrite subst_elimSuccHypTy'.
    * eapply lrefl, simple_app'Valid.
      2: unshelve (now eapply natElimCongValid); tea.
      eapply appcongValid'; tea.
      1: unshelve (eapply irrValidTm; tea; now eapply natValid); tea; now eapply lrefl.
      erewrite <- WeakeningCompute.subst_arr'. do 2 f_equal.
      rewrite to_subst_sound with (σ:=n..), subst_ren_subst_up. f_equal.
      rewrite <- up_to_subst, <- to_subst_sound. rewrite up_wk1_ren_on. now bsimpl.
      Unshelve.
      eapply simpleArr'Valid; tea; now eapply substS.
  Qed.

End NatElimRedValid.

End Nat.

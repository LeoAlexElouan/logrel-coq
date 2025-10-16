From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe SimpleArr Application Bool Nat.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Bool.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.

Lemma boolValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tBool | VΓ].
Proof.
  unshelve econstructor; intros; now eapply boolRed.
Defined.

Lemma boolValidU {Γ} (VΓ : [||-v Γ]):  [Γ ||-v<one> tBool : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply boolTermRed.
Qed.

Lemma trueValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']):
  [Γ ||-v<l> tTrue : tBool | VΓ | boolValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply trueRed; tea.
  3: now eapply boolRedTy.
Qed.

Lemma falseValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']):
  [Γ ||-v<l> tFalse : tBool | VΓ | boolValid VΓ].
Proof.
  constructor; intros; cbn; unshelve eapply falseRed; tea.
  3: now eapply boolRedTy.
Qed.


Section BoolElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := boolValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN).

  Lemma boolElimCongValid {P P' ht ht' hf hf'}
    (VP : [Γ ,, tBool ||-v<l> P ≅ P' | VΓN ])
    (VPt := substS VP (trueValid VΓ))
    (Vht : [Γ ||-v<l> ht ≅ ht' : P[tTrue..] | VΓ | VPt])
    (VPf := substS VP (falseValid VΓ))
    (Vhf : [Γ ||-v<l> hf ≅ hf' : P[tFalse..] | VΓ | VPf])
    {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tBool | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tBoolElim P ht hf n ≅ tBoolElim P' ht' hf' n' : _ | VΓ | VPn].
  Proof.
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VN Vσσ').
    instValid Vuσ; cbn in *.
    eapply irrLREq. 1: now rewrite singleSubstComm'.
    unshelve eapply boolElimRedEq; tea.
    3-5: now escape.
    + now eapply boolRedTy.
    + intros ?? Rn; rewrite 2!up_single_subst; unshelve eapply validTyExt; cycle 3; tea.
      now unshelve econstructor.
    + eapply irrLREq; tea; now rewrite singleSubstComm'.
    + eapply irrLREq; tea; now rewrite singleSubstComm'.
  Qed.
End BoolElimValid.

Lemma boolElimValid {Γ Γ' l P ht ht' hf hf' n n'}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := boolValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tBool ||-v<l> P | VΓN])
    (VPt := substS VP (trueValid VΓ))
    (Vht : [Γ ||-v<l> ht ≅ ht' : P[tTrue..] | VΓ | VPt])
    (VPf := substS VP (falseValid VΓ))
    (Vhf : [Γ ||-v<l> hf ≅ hf' : P[tFalse..] | VΓ | VPf])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tBoolElim P ht hf  n : _ | VΓ | VPn].
Proof. now eapply lrefl, boolElimCongValid. Qed.

Section BoolElimRedValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := boolValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' ht ht' hf hf'}
    (VP : [Γ ,, tBool ||-v<l> P ≅ P' | VΓN ])
    (VPt := substS VP (trueValid VΓ))
    (Vht : [Γ ||-v<l> ht ≅ ht' : P[tTrue..] | VΓ | VPt])
    (VPf := substS VP (falseValid VΓ))
    (Vhf : [Γ ||-v<l> hf ≅ hf' : P[tFalse..] | VΓ | VPf]).

  Lemma boolElimTrueValid  :
    [Γ ||-v<l> tBoolElim P ht hf tTrue ≅ ht : _ | VΓ | VPt].
  Proof.
    eapply redSubstValid. 2: now eapply lrefl.
    constructor; intros; cbn; rewrite singleSubstComm'.
    instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
    eapply redtm_boolElimTrue; tea.
    + now rewrite <- (singleSubstComm' _ tTrue σ).
    + now rewrite <- (singleSubstComm' _ tFalse σ).
  Qed.

  Lemma boolElimFalseValid  :
    [Γ ||-v<l> tBoolElim P ht hf tFalse ≅ hf : _ | VΓ | VPf].
  Proof.
    eapply redSubstValid. 2: now eapply lrefl.
    constructor; intros; cbn; rewrite singleSubstComm'.
    instValid Vσσ'; instValid (liftSubst' VN Vσσ'); escape.
    eapply redtm_boolElimFalse; tea.
    + now rewrite <- (singleSubstComm' _ tTrue σ).
    + now rewrite <- (singleSubstComm' _ tFalse σ).
  Qed.

End BoolElimRedValid.

End Bool.

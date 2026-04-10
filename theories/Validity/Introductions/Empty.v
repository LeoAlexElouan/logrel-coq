From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import  Properties.
From LogRel.LogicalRelation.Introductions Require Import Empty.
From LogRel.Validity Require Import Validity Irrelevance Properties Universe Pi SimpleArr Var Application.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Empty.
Context `{GenericTypingProperties}.

Lemma emptyValid {Γ Γ' l} (VΓ : [||-v Γ ≅ Γ']) : [Γ ||-v<l> tEmpty | VΓ].
Proof.
  constructor; intros; now apply emptyRed.
Defined.

Lemma emptyValidU {Γ Γ'} (VΓ : [||-v Γ ≅ Γ']):  [Γ ||-v<one> tEmpty : U | VΓ | UValid VΓ].
Proof.
  constructor; intros; eapply Wpack_return, emptyTermRed.
Qed.


Section EmptyElimValid.
  Context {Γ Γ' l}
    (VΓ : [||-v Γ ≅ Γ'])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    { P P' }
    (VP : [Γ ,, tEmpty ||-v<l> P ≅ P' | VΓN]).

  Lemma emptyElimCongValid {n n'}
    (Vn : [Γ ||-v<l> n ≅ n' : tEmpty | VΓ | VN])
    (VPn := substS VP Vn)
    : [Γ ||-v<l> tEmptyElim P n ≅ tEmptyElim P' n' : _ | VΓ | VPn].
  Proof.
    constructor; intros; instValid Vσσ'; epose proof (Vuσ := liftSubst' VN Vσσ').
    instValid Vuσ; escape.
    eapply irrLREq. 1: now rewrite subst_ren_subst_up.
    change (tEmptyElim ?P ?n)[?σ] with (tEmptyElim P[up_subst σ] n[σ]).
    unshelve eapply emptyElimRedEq; rewrite ?elimSuccHypTy_subst; tea.
(*     + now apply emptyRedTy. *)
    + clear dependent n; clear dependent n'; intros Ξ wfΞ ρΞ ?? Rnn'.
      rewrite 2subst_ren_wk, 2to_subst_sound, 2subst_comp_on.
      unshelve (eapply validTyExt, irrelevanceSubstEqExt, consWkSubstEq; tea); tea.
      all: now rewrite eq_upwk.
  Qed.
End EmptyElimValid.

Lemma emptyElimValid {Γ l P n n'}
    (VΓ : [||-v Γ])
    (VN := emptyValid (l:=l) VΓ)
    (VΓN := validSnoc VΓ VN)
    (VP : [Γ ,, tEmpty ||-v<l> P | VΓN])
    (Vn : [Γ ||-v<l> n ≅ n' : _ | VΓ | VN])
    (VPn := substS VP Vn):
    [Γ ||-v<l> tEmptyElim P n : _ | VΓ | VPn].
Proof.
  eapply lrefl , emptyElimCongValid; tea.
Qed.

End Empty.

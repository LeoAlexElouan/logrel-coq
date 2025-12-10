From Stdlib Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly.
From LogRel.Validity Require Import Validity Irrelevance Properties Introductions.Universe.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.


Section PolyValidity.

  Context `{GenericTypingProperties}.

  Context {l Γ Γ' F F' G G'} (VΓ : [||-v Γ ≅ Γ'])
    (VF : [Γ ||-vS< l > F ≅ F' | VΓ ])
    (VG : [Γ ,, F ||-vS< l > G ≅ G' | validSnoc VΓ VF]).

  Context {Δ σ σ'} (wfΔ : [ |-[ ta ] Δ]) (Vσ : [VΓ | Δ ||-v σ ≅ σ' : _ | wfΔ]).

  Lemma substPolyRed : PolyRed Δ l F[σ] F'[σ'] G[up_term_term σ] G'[up_term_term σ'].
  Proof.
    opector.
    - intros; eapply SwkLR; tea; now eapply SvalidTyExt.
    - intros. rewrite 2!eq_subst_2.
      eapply WAd_return.
      now unshelve now eapply SvalidTyExt; tea; eapply consWkSubstEq.
  Qed.


  Lemma substParamRedTy {T}
    (wtyT : forall Γ A B, [Γ |- A] -> [Γ,, A |- B] -> [Γ |- T A B])
    (convT : forall Γ A A' B B', [Γ |- A] -> [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] -> [Γ |- T A B ≅ T A' B']) :
    ParamRedTy T Δ l (T F[σ] G[up_term_term σ]) (T F'[σ'] G'[up_term_term σ']).
  Proof. apply mkParamRedTy; tea; apply substPolyRed. Qed.

End PolyValidity.



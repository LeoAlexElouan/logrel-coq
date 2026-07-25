(** * LogRel.Introductions.Var : Validity of variables. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe.
From LogRel.Validity Require Import Validity Irrelevance Properties.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Var.
  Context `{GenericTypingProperties}.

  Lemma var0Valid {Γ Γ' l A A'} (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v<l> A ≅ A'| VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | validSnoc VΓ VA | wk1ValidTy _ VA ].
  Proof.
    constructor; intros; cbn; epose (eqHead Vσσ').
    eapply irrLREq; tea; now bsimpl.
  Qed.


  Lemma var0Valid' {Γ Γ' l} {A A' : term} (VΓ : [||-v Γ,,A ≅ Γ']) (VA : [Γ,,A ||-v<l> A⟨@wk1 Γ A⟩ ≅ A' | VΓ]) :
    [Γ,, A ||-v<l> tRel 0 : _ | VΓ | VA ].
  Proof.
    pose proof (invValidity VΓ) as (?&?&?&?&?&e&h); subst; cbn in h; subst.
    constructor; intros; cbn; eapply irrLREqCum;[| exact (eqHead Vσσ')].
    now rewrite wk1_subst.
  Qed.

  Lemma in_ctx_valid {Γ : context} {A : term} {n} (hin : in_ctx Γ n A)
    : forall {Γ'} (VΓ : [||-v Γ ≅ Γ']), ∑ l B, [Γ ||-v<l> A ≅ B | VΓ].
  Proof.
    pattern Γ, n, A, hin.
    eapply term_in_ctx_induction; clear Γ A n hin; intros.
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA &e&?); subst; cbn in *; subst.
      do 2 eexists; now eapply wkValidTy.
    + destruct A' as [A' | ℓ'].
      - pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA &e&?); subst; cbn in *; subst.
        destruct (IH _ VΓ') as (?&?&?).
        do 2 eexists; now eapply wkValidTy.
      - pose proof (invValidity VΓ) as (?&?&?&VΓ'&Vℓ &e&?); subst; cbn in *; subst.
        destruct (IH _ VΓ') as (?&?&?).
        do 2 eexists; now eapply wkValidTy.
  Qed.


  Lemma varnValid {Γ} {A : term} {n} (hin : in_ctx Γ n A) :
    forall l {Γ' A'} (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v<l> A ≅ A' | VΓ]),
      [Γ ||-v<l> tRel n : _ | VΓ | VA ].
  Proof.
    pattern Γ, n, A, hin.
    eapply term_in_ctx_induction; clear Γ A n hin; intros.
    1: eapply var0Valid'.
    destruct A' as [A' | ℓ'].
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&VA'&?&h) ; subst; cbn in h; subst.
      destruct (in_ctx_valid hin VΓ') as (?&?&h).
      pose proof (h' := wk1ValidTm VA' _ (IH _ _ _ _ h)).
      cbn -[wk1] in h'; rewrite wk1_ren in h'; unfold shift in h'.
      unshelve (eapply irrValidTm; tea; eapply wk1ValidTy).
      5: eapply irrValidTy; tea; now eapply lrefl.
      3: now eapply lrefl, convValidTy.
      1: now eapply lrefl.
    + pose proof (invValidity VΓ) as (?&?&?&VΓ'&Vℓ'&?&h) ; subst; cbn in h; subst.
      destruct (in_ctx_valid hin VΓ') as (?&?&h).
      replace (tRel (S n)) with (tRel n)⟨@wk1 Γ ℓ'⟩
       by now rewrite wk1_ren_on.
      assert (VΓℓ : [||-v Γ,, ℓ' ≅ Γ,, ℓ']) by eapply lrefl, validSnocℓ, Vℓ'.
      eapply irrValidTm with (VΓ01:=VΓℓ), wkValidTm with (VΔ := VΓℓ), IH with (VA:=h).
      eapply irrValidTy, lrefl, VA.
      eapply lrefl, validSnocℓ, Vℓ'.
  Qed.

  Lemma var1Valid {Γ l} {A : term} {B} (VΓ : [||-v (Γ,, A) ,, B]) (VA : [_ ||-v<l> A⟨@wk1 Γ A⟩⟨@wk1 (Γ,,A) B⟩ | VΓ]) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ].
  Proof.
    eapply varnValid. rewrite 2 wk_decl.
    now eapply in_there', in_here'.
  Qed.

  Lemma var1Valid' {Γ Γ' l} {A : term} {B} {A' : term} (VΓ : [||-v (Γ,, A) ,, B ≅ Γ']) (VA : [_ ||-v<l> A⟨@wk1 Γ A⟩⟨@wk1 (Γ,,A) B⟩ ≅ A' | VΓ]) :
    [(Γ,, A) ,, B ||-v<l> tRel 1 : _ | VΓ | VA ].
  Proof.
    eapply varnValid. rewrite 2 wk_decl.
    now eapply in_there', in_here'.
  Qed.

End Var.
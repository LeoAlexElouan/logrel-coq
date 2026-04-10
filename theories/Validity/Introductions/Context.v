From LogRel Require Import Utils Syntax.All GenericTyping (* LogicalRelation Monad *).
(* From LogRel.LogicalRelation Require Import Properties. *)
From LogRel.Validity Require Import Validity Irrelevance Properties.

Section Context.
  Context `{GenericTypingProperties}.
  Lemma validFcontext L : [||-v fromFctx L ].
  Proof.
    induction L.
    + eapply validEmpty.
    + eapply validSnocε; tea.
      reflexivity.
  Qed.


  Lemma validConNew (Γ Γ': context) (i i': list_index _) (new new' : newnat _) (b : bool)
    (VΓ : [||-v Γ ≅ Γ']) (eqi : i = i' :> nat) (eqnew : new = new' :> nat) :
    [||-v Γ,, i : new ↦ b ≅ Γ',,i' : new' ↦ b].
  Proof.
    revert i i' new new' eqi eqnew.
    indValid VΓ.
    + intros. destruct i.
    + intros * VΓ VF IH * ??.
      destruct i, i' as [|i']; [|inversion eqi..|].
      - eapply validSnocε, Fequiv_Fup; tea.
      - change ((fromFctx ?L,, ↦ ?F),, index_S ?i : ?new ↦ b) with (fromFctx L,, i : new ↦ b,, ↦ F).
        eapply validSnocε; tea.
        eapply IH; tea. cbn in eqi. now inversion eqi.
    + intros * VA IH * ??.
      change (?Γ,,?A,, ?i : ?new ↦ b) with (Γ,, i : new ↦ b,, A).
      unshelve eapply validSnoc.
      - exact l.
      - eapply IH; tea.
      - rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ A').
        erewrite <-2 (wk_Fstep_ren_on (i : list_index Γ) (new : newnat (list_at Γ i)) b).
        eapply wkValidTy, VA.
  Qed.

  Lemma validConAlpha (Γ Γ' : context) (VΓ : [||-v Γ ≅ Γ']) : [||-v Γ,,↦ Fnil ≅ Γ',, ↦ Fnil].
  Proof.
    indValid VΓ.
    + eapply validFcontext.
    + intros * VF VΓ IH.
      eapply validSnocε.
      eapply validSnocε; tea.
      reflexivity.
    + intros * VA IH.
      change (?Γ,, ?A,, ↦ Fnil) with (Γ,,↦ Fnil ,, ren_alpha S A).
      unshelve eapply validSnoc.
      - exact l.
      - eapply IH.
      - rewrite <- (wk_id_ren_on Γ A), <- (wk_id_ren_on Γ A').
        rewrite <-2 (wk_alphastep_ren_on (F:=Fnil)).
        eapply wkValidTy, VA.
  Qed.

End Context.
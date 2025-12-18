From LogRel Require Import Utils Syntax.All GenericTyping Monad LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.

Set Universe Polymorphism.
Set Printing Universes.
Set Printing Primitive Projection Parameters.

Section UniverseReducibility.
  Context `{GenericTypingProperties}.

  Lemma redUOneCtx {Γ} : [|- Γ] -> [Γ ||-U<one> U ≅ U].
  Proof.
    intros ; econstructor; [easy| gen_typing|eapply redtywf_refl; gen_typing].
  Defined.

(*   Lemma redUOne {Γ l A} : [|- Γ] -> [Γ ||-<l> A] -> [Γ ||-U<one> U ≅ U].
  Proof.
    intros wfΓ hA; (escapeSplit wfΓ); eapply redUOneCtx.
  Defined.
 *)
  Lemma UnivEq'@{i j k l} {Γ A B l} (rU : [ LogRel@{i j k l} l | Γ ||- U ≅ U ]) (rA : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU])
    : [ LogRel@{i j k l} zero | Γ ||- A ≅ B].
  Proof.
    escape; assert ([|-Γ]) as wfΓ by gtyping.
    now assert [ LogRel@{i j k l} one | Γ ||- A ≅ B : U | LRU_@{i j k l} (redUOneCtx wfΓ)]
      as [??? hA%redTyRecFwd%cumLR]
    by (eapply SirrLREqCum; tea; reflexivity).
  Qed.

  Lemma SUnivEq@{i j k l} {Γ A B l} l' (rU : [ LogRel@{i j k l} l | Γ ||- U ≅ U]) (rA : [ LogRel@{i j k l} l | Γ ||- A ≅ B : U | rU])
    : [ LogRel@{i j k l} l' | Γ ||- A ≅ B].
  Proof.
    destruct l'.
    - eapply (UnivEq' rU rA).
    - econstructor. eapply LR_embedding.
      + exact Oi.
      + apply (UnivEq' rU rA).
  Qed.

  Lemma UnivEq@{i j k l} {Γ A B l} l' (rU : WLRAdequate@{i j k l} Γ l U U) (rA : [ Γ ||-< l > A ≅ B : U | rU])
    : WLRAdequate@{i j k l} Γ l' A B.
  Proof.
    eapply (dSplit_bind_return rA).
    intros ??? orU orA.
    eapply SUnivEq.
    now unshelve now eapply rA.
  Qed.

End UniverseReducibility.

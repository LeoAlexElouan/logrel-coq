From Stdlib Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Poly.

Set Universe Polymorphism.

Section PolyRedPi.
  Context `{GenericTypingProperties}.

  Lemma LRPiPoly0 {Γ l A A' B B'} (wfΓ : [|- Γ]) (PAB : PolyRed Γ l A A' B B') : [Γ ||-Π<l> tProd A B ≅ tProd A' B'].
  Proof.
    eapply mkParamRedTy; tea; intros; gtyping.
  Defined.

  Definition LRPiPoly {Γ l A A' B B'} (wfΓ : [|- Γ]) (PAB : PolyRed Γ l A A' B B') :
    [Γ ||-S<l> tProd A B ≅ tProd A' B'] :=
    LRPi' (LRPiPoly0 wfΓ PAB).

End PolyRedPi.



Lemma canonPi `{GenericTypingProperties} {Γ A A' B B' l p p'}
  {RΠ : [Γ ||-S< l > tProd A B ≅ tProd A' B']} :
  [ Γ ||-S< l > p ≅ p' : tProd A B | RΠ] ->
  [ Γ ||-S< l > p ≅ p' : tProd A B | LRPi' (normRedΠ RΠ)].
Proof.
  intro. now eapply SirrLR.
Qed.

Lemma canonPi_inv `{GenericTypingProperties} {Γ A A' B B' l p p'}
  {RΠ : [Γ ||-S< l > tProd A B ≅ tProd A' B']} :
  [ Γ ||-S< l > p ≅ p' : tProd A B | LRPi' (normRedΠ RΠ)] ->
  [ Γ ||-S< l > p ≅ p' : tProd A B | RΠ].
Proof.
  intro. now eapply SirrLR.
Qed.
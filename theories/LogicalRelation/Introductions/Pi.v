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

  Definition Build_PiRedTmEq' {Γ l A B} {ΠA : PiRedTy Γ l A B} {t u : term}
    (shp := PiRedTy.domL ΠA) (shp' := PiRedTy.domR ΠA)
    (pos := PiRedTy.codL ΠA) (pos' := PiRedTy.codR ΠA)
    (redL : PiRedTm ΠA t) (redR : PiRedTm ΠA u)
    (nfL := PiRedTmEq.nf redL) (nfR := PiRedTmEq.nf redR) :
    [Γ |- nfL ≅ nfR : tProd shp pos] ->
    (forall Δ ρ wfΔ a b
      (hab : [Δ ||-S< l > a ≅ b : _ | PolyRed.shpRed ΠA ρ wfΔ ]), 
      [Δ ||-< l > tApp nfL⟨ρ⟩ a ≅ tApp nfR⟨ρ⟩ b : _
        | PolyRed.posRed ΠA ρ wfΔ hab]) ->
    [Γ ||-Π t ≅ u : A | ΠA].
  Proof.
    intros eq eqApp.
    econstructor.
    1: eapply eq.
    intros Δ a b ρ wfΔ hab.
    eapply eqApp.
  Qed.



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
End PolyRedPi.
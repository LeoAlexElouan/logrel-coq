From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Universe Bool Def.


Module EllRedTmEq.
Section EllRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta} {l : TypeLevel} {Γ : context} {RNtoB : [Γ ||-S<l> arr' Γ tNat tBool] } {ℓ : ell}.

  Inductive isLREll : term -> Type :=
  | boxLREll {t} : [Γ ||-S< l > t : arr' Γ tNat tBool | RNtoB] ->
    (forall n b, in_ell ℓ n b ->
      [ Γ ||-Bool tApp t (nat_to_term n) ≅ bool_to_term b :Bool]) ->
    isLREll (tBox ℓ t)
  | neLREll {v} : in_ctx Γ v ℓ -> isLREll (tRel v).

  Record EllRedTmEq tL tR : Type := {
    isellL : isLREll tL;
    isellR : isLREll tR;
    gL : [Γ |- tL : ℓ];
    gR : [Γ |- tR : ℓ];
    eq : [Γ |- tL ≅ tR : ℓ];
    eqeval : [Γ ||-S< l > tEval ℓ tL ≅ tEval ℓ tR : _ | RNtoB];
    }.

(*   Inductive EllRedTmEq : term -> term -> Type :=
  | boxReq {t t'} : [Γ ||-S< l > t ≅ t' : arr' Γ tNat tBool | RNtoB ] ->
    (forall n b, in_ell ℓ n b ->
      [ Γ ||-Bool tApp t (nat_to_term n) ≅ bool_to_term b :Bool]) ->
    EllRedTmEq (tBox ℓ t) (tBox ℓ t')
  | neRed {v} : in_ctx Γ v ℓ -> EllRedTmEq (tRel v) (tRel v).
 *)
(*   Section Def.
    Context `{!GenericTypingProperties _ _ _ _ _ _ _ _ _}.

    Lemma NatPropEq_isNat {t t' : term} :
      NatPropEq t t' -> isNat t × isNat t'.
    Proof.
      intros [| |?? []]; split; econstructor.
      all: eapply convneu_whne; eassumption + now symmetry.
    Defined.

  End Def. *)


End EllRedTmEq.
Arguments EllRedTmEq {_ _ _ _ _ _ _ _ _ _}.
End EllRedTmEq.

Export EllRedTmEq(EllRedTmEq).
Notation "[ Γ ||-EllS t ≅ u : ℓ | RNtoB ]" := (EllRedTmEq Γ RNtoB ℓ t u) 
  (at level 0, Γ, t, u, ℓ, RNtoB at level 50).
Notation "[ Γ ||-EllS t : ℓ | RNtoB ]" := (EllRedTmEq Γ RNtoB ℓ t t) 
  (at level 0, Γ, t, ℓ, RNtoB at level 50).

Section WEllRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.
  Definition WEllRedTmEq {l} Γ (RNtoB : [Γ ||-<l> arr' Γ tNat tBool]) ℓ t u :=
    dSplit (fun Δ _ (ρ: Δ ≤ Γ) hSplit => [ Δ ||-EllS t⟨ρ⟩ ≅ u⟨ρ⟩ : ℓ | hSplit]) RNtoB.
End WEllRedTmEq.

Notation "[ Γ ||-Ell t ≅ u : ℓ | RNtoB ]" := (WEllRedTmEq Γ RNtoB ℓ t u)
  (at level 0, Γ, t, u, ℓ, RNtoB at level 50).
Notation "[ Γ ||-Ell t : ℓ | RNtoB ]" := (WEllRedTmEq Γ RNtoB ℓ t t)
  (at level 0, Γ, t, ℓ, RNtoB at level 50).








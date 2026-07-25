From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All GenericTyping Monad.
From LogRel.LogicalRelation.Definition Require Import Universe Bool Prelude Def Helper.

(*   Lemma SNtoBRed `{GenericTypingProperties} Γ (wfΓ : [|-Γ]) : [Γ ||-S< zero > arr' Γ tNat tBool ].
  Proof.
    assert(gN : [Γ |- tNat]).
    { eapply wft_term, ty_nat; tea. }
    assert (wfΓN : [|-Γ,, tNat]).
    { eapply wfc_cons, wft_term, ty_nat; tea. }
    assert (gB : [Γ,,tNat |- tBool]).
    { eapply wft_term, ty_bool; tea. }
    eapply LRPi'.
    exists tNat tNat tBool tBool.
    1,2: constructor; tea;
      eapply redtywf_refl, wft_prod; tea.
    + eapply convty_term, convtm_nat; tea.
    + eapply convty_prod, convty_term, convtm_bool; tea.
      eapply convty_term, convtm_nat; tea.
    + unshelve econstructor.
      - intros * wfΔ.
        apply LRNat_.
        constructor; eapply redtywf_refl, wft_term, ty_nat; tea.
      - intros * _.
        eapply Split_return; tea.
        intros Ξ wfΞ ρΞ.
        apply LRBool_.
        constructor; eapply redtywf_refl, wft_term, ty_bool; tea.
  Qed.
 *)
Module EllRedTmEq.
Section EllRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.

  Record EllAdequate Γ l (ℓ ℓ' : ell) := {
    NtoBAd : [Γ ||-S< l > arr' Γ tNat tBool];
    elleqAd : ℓ = ℓ'
    }.
  Arguments NtoBAd {_ _ _ _}.
  Notation "[ Γ ||-EllS< l > ℓ ≅ ℓ' ]" := (EllAdequate Γ l ℓ ℓ') (at level 0, Γ, l, ℓ, ℓ' at level 50).
  Notation "[ Γ ||-EllS< l > ℓ ]" := (EllAdequate Γ l ℓ ℓ) (at level 0, Γ, l, ℓ at level 50).

  Context {ℓ ℓ': ell} {l Γ} (Rℓ : [Γ ||-EllS< l > ℓ ≅ ℓ']) (* {RNtoB : [Γ ||-S<l> arr' Γ tNat tBool] } *) .

  Inductive isLREll : term -> Type :=
  | boxLREll {t} : [Γ ||-S< l > t : arr' Γ tNat tBool | Rℓ.(NtoBAd) ] ->
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
    eqeval : [Γ ||-S< l > tEval ℓ tL ≅ tEval ℓ tR : _ | Rℓ.(NtoBAd)];
    }.

  Definition EllPack : LRPack Γ ℓ ℓ' := {| LRPack.eqTm := EllRedTmEq |}.

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
Arguments EllRedTmEq {_ _ _ _ _ _ _ _ _ _ _ _}.
End EllRedTmEq.

Export EllRedTmEq(EllRedTmEq,EllAdequate).
#[warnings="-uniform-inheritance"]Coercion EllRedTmEq.EllPack : EllAdequate >-> LRPack.


(* Notation "[ Γ ||-EllS t ≅ u : ℓ | RNtoB ]" := (EllRedTmEq Γ RNtoB ℓ t u) 
  (at level 0, Γ, t, u, ℓ, RNtoB at level 50).
Notation "[ Γ ||-EllS t : ℓ | RNtoB ]" := (EllRedTmEq Γ RNtoB ℓ t t) 
  (at level 0, Γ, t, ℓ, RNtoB at level 50).
 *)
Section WEllRedTmEq.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{ConvType ta}
    `{RedType ta} `{Typing ta} `{ConvNeuConv ta} `{ConvTerm ta}
    `{RedTerm ta}.
  Definition WEllAdequate Γ l ℓ ℓ' :=
    Split (fun Δ _ (_ : Δ ≤ Γ) => EllAdequate Δ l ℓ ℓ').

  Definition WEllpack {Γ l ℓ ℓ'} (RA : WEllAdequate Γ l ℓ ℓ') : LRPack Γ ℓ ℓ' :=
    Build_LRPack _ _ _ (fun t u =>
      dSplit (fun Δ _ (ρ: Δ ≤ Γ) (hSplit : EllAdequate _ _ _ _) => [ Δ ||-S< l > t⟨ρ⟩ ≅ u⟨ρ⟩ : _ | hSplit]) RA).

  Coercion WEllpack : WEllAdequate >-> LRPack.
End WEllRedTmEq.

Notation "[ Γ ||-EllS< l > ℓ ≅ ℓ' ]" := (EllAdequate Γ l ℓ ℓ')
  (at level 0, Γ, l, ℓ at level 50).
Notation "[ Γ ||-EllS< l > ℓ ]" := (EllAdequate Γ l ℓ ℓ)
  (at level 0, Γ, l, ℓ at level 50).
Notation "[ Γ ||-Ell< l > ℓ ≅ ℓ' ]" := (WEllAdequate Γ l ℓ ℓ')
  (at level 0, Γ, l, ℓ at level 50).
Notation "[ Γ ||-Ell< l > ℓ ]" := (WEllAdequate Γ l ℓ ℓ)
  (at level 0, Γ, l, ℓ at level 50).
(* Notation "[ Γ ||-Ell t : ℓ | RNtoB ]" := (WEllRedTmEq Γ RNtoB ℓ t t)
  (at level 0, Γ, t, ℓ, RNtoB at level 50).
 *)







(** * LogRel.Validity.Validity: definition of validity: closure of the logical relation under substitution. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation LogicalRelation.Properties.
From Equations Require Import Equations.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Create HintDb substitution.
#[global] Hint Constants Opaque : substitution.
#[global] Hint Variables Transparent : substitution.
Ltac substitution := eauto with substitution.


(* The type of our inductively defined validity relation:
  for some R : VRel, R Γ Γ' eqSubst says
  that according to R, Γ and Γ' are validly convertible and the associated
  substitution equality is eqSubst.
  One should think of VRel as a functional relation taking two arguments Γ, Γ'
  and returning eqSubst as an output *)
  Inductive Fequiv L L' : Set := Fequiv_make : L ≤ε L' -> L' ≤ε L -> Fequiv L L'.
  Notation "L =ε L'" := (Fequiv L L').
  Instance Equivalence_Fequiv : Equivalence Fequiv.
  Proof.
    split.
    + split; eapply Fwk_id.
    + intros ?? []; now split.
    + intros ??? [] []; split; now eapply Fwk_compose.
  Qed.

  Definition lFwk {L L'} (eq : L =ε L') : L ≤ε L'.
  Proof. apply eq. Qed.

  Definition rFwk {L L'} (eq : L =ε L') : L' ≤ε L.
  Proof. apply eq. Qed.

  Lemma Fequiv_Fup {L L'} {b} (eq : L =ε L') {new : newnat L} {new' : newnat L'} :
   new = new' :> nat -> (Fcons' L' new' b) =ε (Fcons' L new b).
  Proof.
    destruct eq.
    intros e; split; eapply Fwk_Fup; tea.
    now symmetry.
  Qed.

  Definition VRel@{i j | i < j +} `{ta : tag} `{!WfContext ta} :=
  forall (Γ Γ' : context)
    (eqSubst : forall (Δ : context) (wfΔ : [|- Δ ]) (σ σ' : substitution) , Type@{i})
    , Type@{j}.

(* A VPack contains the data corresponding to the codomain of VRel seen as a functional relation *)

Module VPack.

  Record VPack@{i} `{ta : tag} `{!WfContext ta} {Γ Γ' : context} :=
  {
    eqSubst : forall (Δ : context) (wfΔ : [|- Δ ]) (σ σ' : substitution) , Type@{i} ;
  }.

  Arguments VPack : clear implicits.
  Arguments VPack {_ _}.
  Arguments Build_VPack {_ _}.
End VPack.

Export VPack(VPack,Build_VPack).

Notation "[ P | Δ ||-v σ : Γ | wfΔ ]" := (VPack.eqSubst (Γ:=Γ) P Δ wfΔ σ σ) (at level 0, P, Δ, σ, Γ, wfΔ at level 50).
Notation "[ P | Δ ||-v σ : Γ ≅ Γ' | wfΔ ]" := (VPack.eqSubst (Γ:=Γ) (Γ':=Γ') P Δ wfΔ σ σ) (at level 0, P, Δ, σ, Γ, Γ', wfΔ at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ | wfΔ ]" := (VPack.eqSubst (Γ:=Γ) P Δ wfΔ σ σ') (at level 0, P, Δ, σ, σ', Γ, wfΔ at level 50).
Notation "[ P | Δ ||-v σ ≅ σ' : Γ ≅ Γ' | wfΔ ]" := (VPack.eqSubst (Γ:=Γ) (Γ':=Γ') P Δ wfΔ σ σ') (at level 0, P, Δ, σ, σ', Γ, Γ', wfΔ at level 50).

(* An VPack it adequate wrt. a VRel when its three unpacked components are *)
#[universes(polymorphic)] Definition VPackAdequate@{i j} `{ta : tag} `{!WfContext ta}
  (R : VRel@{i j}) {Γ Γ' : context} (P : VPack@{i} Γ Γ') : Type@{j} :=
  R Γ Γ' P.(VPack.eqSubst).

Arguments VPackAdequate {_ _} _ {_ _} _ /.

Module VAd.

  Record > VAdequate `{ta : tag} `{!WfContext ta} {R : VRel} {Γ Γ' : context} :=
  {
    pack :> VPack Γ Γ' ;
    adequate :> VPackAdequate R pack
  }.

  Arguments VAdequate : clear implicits.
  Arguments VAdequate {_ _}.
  Arguments Build_VAdequate {_ _ _ _ _}.

End VAd.

Export VAd(VAdequate,Build_VAdequate).
(* These coercions would be defined using the >/:> syntax in the definition of the record,
  but this fails here due to the module being only partially exported *)
Coercion VAd.pack : VAdequate >-> VPack.
Coercion VAd.adequate : VAdequate >-> VPackAdequate.

Notation "[ R | ||-v Γ ]"                            := (VAdequate R Γ Γ) (at level 0, R, Γ at level 50).
Notation "[ R | ||-v Γ ≅ Γ' ]"                       := (VAdequate R Γ Γ') (at level 0, R, Γ, Γ' at level 50).
Notation "[ R | Δ ||-v σ : Γ | RΓ | wfΔ ]"           := (RΓ.(@VAd.pack _ _ R Γ _).(VPack.eqSubst) Δ wfΔ σ σ) (at level 0, R, Δ, σ, Γ, RΓ, wfΔ at level 50).
Notation "[ R | Δ ||-v σ ≅ σ' : Γ | RΓ | wfΔ ]" := (RΓ.(@VAd.pack _ _ R Γ _).(VPack.eqSubst) Δ  wfΔ σ σ') (at level 0, R, Δ, σ, σ', Γ, RΓ, wfΔ at level 50).

Record StypeValidity@{u i j k l} `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {Γ Γ' : context} {VΓ : VPack@{u} Γ Γ'}
  {l : TypeLevel} {A A' : term} :=
  {
    SvalidTyExt : forall {Δ : context} (wfΔ : [|- Δ ])
      {σ σ' : substitution}
      (vσσ' : [ VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ ])
      , [LogRel@{i j k l} l | Δ ||- A [ σ ] ≅ A' [ σ' ] ]
  }.

Arguments StypeValidity : clear implicits.
Arguments StypeValidity {_ _ _ _ _ _ _ _ _}.

Record typeValidity@{u i j k l} `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {Γ Γ' : context} {VΓ : VPack@{u} Γ Γ'}
  {l : TypeLevel} {A A' : term} :=
  {
    validTyExt : forall {Δ : context} (wfΔ : [|- Δ ])
      {σ σ' : substitution}
      (vσσ' : [ VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ ]),
      WLRAdequate@{i j k l} Δ l A[σ] A'[σ']
  }.

Arguments typeValidity : clear implicits.
Arguments typeValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ P | Γ ||-vS< l > A ≅ B ]" := (StypeValidity Γ _ P l A B) (at level 0, P, Γ, l, A, B at level 50).
Notation "[ P | Γ ||-v< l > A ≅ B ]" := (typeValidity Γ _ P l A B) (at level 0, P, Γ, l, A, B at level 50).

Lemma validTy_return `{GenericTypingProperties} {Γ Γ'} {VΓ : VPack Γ Γ'} {l A B} :
  [ VΓ | Γ ||-vS< l > A ≅ B ] -> [ VΓ | Γ ||-v< l > A ≅ B ].
Proof.
  intros vAB.
  constructor.
  intros.
  eapply WAd_return.
  now eapply vAB.
Qed.


Definition emptyEqSubst@{u} `{ta : tag} `{!WfContext ta}
  (Δ : context) (wfΔ : [|- Δ]) (σ σ' : substitution): Type@{u} :=
    unit.

Definition emptyVPack `{ta : tag} `{!WfContext ta} : VPack ε ε :=
  Build_VPack _ _ emptyEqSubst.

Section εsnocValid.
  Universe u k l.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {L L': list Fcontext} (Γ := fromFctx L) (Γ' := fromFctx L') {VΓ : VPack@{u} Γ Γ'} {F F' : Fcontext} (* {l : TypeLevel} *).
(*   {vA : typeValidity@{u i j k l} Γ Γ' VΓ l A A' (* [ VΓ | Γ ||-v< l > A ] *)}. *)


  Record εsnocEqSubst (VF : F =ε F') {Δ : context} {wfΔ : [|- Δ]} {σ σ' : substitution} : Type := {
      εeqTail : [ VΓ | Δ ||-v εtail_subst σ ≅ εtail_subst σ' : Γ | wfΔ ] ;
      εeqHedIndex : list_index Δ.(Fctx) ; 
      εeqHeadIn : (subst_alpha σ 0) = index_to_nat εeqHedIndex ;
      εeqHead : list_at Δ.(Fctx) εeqHedIndex ≤ε F ;
    }.

  Definition εsnocVPack (VF : F =ε F') := Build_VPack@{u} (Γ ,, ↦ F) (Γ',, ↦ F') (@εsnocEqSubst VF).
End εsnocValid.

Arguments εsnocEqSubst : clear implicits.
Arguments εsnocEqSubst {_ _}.

Arguments εsnocVPack : clear implicits.
Arguments εsnocVPack {_ _}.

Section snocValid.
  Universe u i j k l.
  Context `{ta : tag} `{!WfContext ta}
  `{!WfType ta} `{!Typing ta} `{!ConvType ta}
  `{!ConvTerm ta} `{!ConvNeuConv ta} `{!RedType ta} `{!RedTerm ta}
  {Γ Γ': context} {VΓ : VPack@{u} Γ Γ'} {A A' : term} {l : TypeLevel}
  {vA : typeValidity@{u i j k l} Γ Γ' VΓ l A A' (* [ VΓ | Γ ||-v< l > A ] *)}.


  Record snocEqSubst {Δ : context} {wfΔ : [|- Δ]} {σ σ' : substitution} : Type :=
    {
      eqTail : [ VΓ | Δ ||-v tail_subst σ ≅ tail_subst σ' : Γ | wfΔ ] ;
      eqHead : [ Δ ||-< l > (subst_subst σ) var_zero ≅ (subst_subst σ') var_zero : A[tail_subst σ] | validTyExt vA wfΔ eqTail ]
    }.

  Definition snocVPack := Build_VPack@{u (* max(u,k) *)} (Γ ,, A) (Γ',,A') (@snocEqSubst).
End snocValid.

Arguments snocEqSubst : clear implicits.
Arguments snocEqSubst {_ _ _ _ _ _ _ _ _}.

Arguments snocVPack : clear implicits.
Arguments snocVPack {_ _ _ _ _ _ _ _ _}.

Unset Elimination Schemes.

Inductive VR@{i j k l} `{ta : tag}
  `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta}
  `{RedType ta} `{RedTerm ta} : VRel@{k l} :=
  | VREmpty : VR ε ε emptyEqSubst@{k}
  | VRSnocε : forall {L L' : list Fcontext} (Γ:= fromFctx L) (Γ' := fromFctx L') {F F'}
    (VΓ : VPack@{k} Γ Γ')
    (VΓad : VPackAdequate@{k l} VR VΓ)
     (VF : F =ε F'), (* let ΓF := (Γ ,, ↦ F) in *)
    VR (Γ ,, ↦ F) (Γ' ,, ↦ F') (εsnocEqSubst@{k k l} Γ Γ' VΓ F F' VF)
  | VRSnoc : forall {Γ Γ':context} {A A' l}
    (VΓ : VPack@{k} Γ Γ')
    (VΓad : VPackAdequate@{k l} VR VΓ)
    (VA : typeValidity@{k i j k l} Γ Γ' VΓ l A A' (*[ VΓ | Γ ||-v< l > A ]*)),
    VR (Γ,,A) (Γ',,A') (snocEqSubst Γ Γ' VΓ A A' l VA).


Set Elimination Schemes.

Notation "[||-v Γ ]"                        := [ VR | ||-v Γ ] (at level 0, Γ at level 50).
Notation "[||-v Γ ≅ Γ' ]"                   := [ VR | ||-v Γ ≅ Γ' ] (at level 0, Γ, Γ' at level 50).
Notation "[ Δ ||-v σ : Γ | VΓ | wfΔ ]"      := [ VR | Δ ||-v σ : Γ | VΓ | wfΔ ]  (at level 0, Δ, σ, Γ, VΓ, wfΔ at level 50).
Notation "[ Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ]" := [ VR | Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ ] (at level 0, Δ, σ, σ', Γ, VΓ, wfΔ at level 50).
Notation "[ Γ ||-vS< l > A | VΓ ]"          := [ VΓ | Γ ||-vS< l > A ≅ A ] (at level 0, Γ, l , A, VΓ at level 50).
Notation "[ Γ ||-vS< l > A ≅ B | VΓ ]"      := [ VΓ | Γ ||-vS< l > A ≅ B ] (at level 0, Γ, l , A, B, VΓ at level 50).
Notation "[ Γ ||-v< l > A | VΓ ]"          := [ VΓ | Γ ||-v< l > A ≅ A ] (at level 0, Γ, l , A, VΓ at level 50).
Notation "[ Γ ||-v< l > A ≅ B | VΓ ]"      := [ VΓ | Γ ||-v< l > A ≅ B ] (at level 0, Γ, l , A, B, VΓ at level 50).


Section MoreDefs.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedType ta} `{RedTerm ta}.

  Definition validEmpty@{i j k l} : [VR@{i j k l}| ||-v ε ≅ ε ] :=
    Build_VAdequate emptyVPack@{k} VREmpty.

  Definition validSnoc@{i j k l} {Γ Γ' : context} {A A' l}
    (VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']) (VA : [Γ ||-v< l > A ≅ A' | VΓ])
    : [||-v Γ ,, A ≅ Γ' ,, A'] :=
    Build_VAdequate (snocVPack Γ Γ' VΓ A A' l VA) (VRSnoc VΓ VΓ VA).

  Definition validSnocε@{i j k l} {L L' : list Fcontext} (Γ:= fromFctx L) (Γ' := fromFctx L') {F F'}
    (VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']) (VF : F =ε F')
    : [||-v Γ ,, ↦ F ≅ Γ' ,, ↦ F'] :=
    Build_VAdequate (εsnocVPack Γ Γ' VΓ F F' VF) (VRSnocε VΓ VΓ VF).


  Record StermEqValidity@{i j k l} {Γ Γ' : context} {l} {A A' : term}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']}
    {VA : StypeValidity@{k i j k l} Γ Γ' VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)} {t u} : Type :=
    {
      SvalidTmExt : forall {Δ}(wfΔ : [|- Δ]) {σ σ'}
         (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ]),
        [Δ ||-<l> t[σ] ≅ u[σ'] : A[σ] | SvalidTyExt VA wfΔ Vσσ']
    }.

  Record StmEqValidity {Γ Γ' : context} {l} {t t' A A' : term} {VΓ : [||-v Γ ≅ Γ']} : Type :=
    {
      SVty  : [Γ ||-vS< l > A ≅ A' | VΓ] ;
      SVeq  : @StermEqValidity Γ Γ' l A A' VΓ SVty t t'
    }.

  Record redValidity {Γ Γ'} {t u A : term} {VΓ : [||-v Γ ≅ Γ']} : Type :=
    {
      validRed : forall {Δ} (wfΔ : [|- Δ]) {σ σ'} (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ]),
        [Δ |- t[σ] ⤳* u[σ] : A[σ]]
    }.



  Record termEqValidity@{i j k l} {Γ Γ' : context} {l} {A A' : term}
    {VΓ : [VR@{i j k l}| ||-v Γ ≅ Γ']}
    {VA : typeValidity@{k i j k l} Γ Γ' VΓ l A A' (*[Γ ||-v<l> A |VΓ]*)} {t u} : Type :=
    {
      validTmExt : forall {Δ}(wfΔ : [|- Δ]) {σ σ'}
         (Vσσ' : [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ]),
        [Δ ||-<l> t[σ] ≅ u[σ'] : A[σ] | validTyExt VA wfΔ Vσσ']
    }.

  Record tmEqValidity {Γ Γ' : context} {l} {t t' A A' : term} {VΓ : [||-v Γ ≅ Γ']} : Type :=
    {
      Vty  : [Γ ||-v< l > A ≅ A' | VΓ] ;
      Veq  : @termEqValidity Γ Γ' l A A' VΓ Vty t t'
    }.



End MoreDefs.

Arguments termEqValidity : clear implicits.
Arguments termEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_termEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments tmEqValidity : clear implicits.
Arguments tmEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_tmEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments StermEqValidity : clear implicits.
Arguments StermEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_StermEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments StmEqValidity : clear implicits.
Arguments StmEqValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_StmEqValidity {_ _ _ _ _ _ _ _ _}.

Arguments redValidity : clear implicits.
Arguments redValidity {_ _ _ _ _ _ _ _ _}.
Arguments Build_redValidity {_ _ _ _ _ _ _ _ _}.

Notation "[ Γ ||-vS< l > t : A | VΓ | VA ]"     := (StermEqValidity Γ _ l A _ VΓ VA t t) (at level 0, Γ, l, t, A, VΓ, VA at level 50).
Notation "[ Γ ||-vS< l > t ≅ u : A | VΓ | VA ]" := (StermEqValidity Γ _ l A _ VΓ VA t u) (at level 0, Γ, l, t, u, A, VΓ, VA at level 50).
Notation "[ Γ ||-vS< l > t ≅ u : A | VΓ ]"      := (StmEqValidity Γ _ l t u A _ VΓ) (at level 0, Γ, l, t, u, A, VΓ at level 50).
Notation "[ Γ ||-v< l > t : A | VΓ | VA ]"     := (termEqValidity Γ _ l A _ VΓ VA t t) (at level 0, Γ, l, t, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ | VA ]" := (termEqValidity Γ _ l A _ VΓ VA t u) (at level 0, Γ, l, t, u, A, VΓ, VA at level 50).
Notation "[ Γ ||-v< l > t ≅ u : A | VΓ ]"      := (tmEqValidity Γ _ l t u A _ VΓ) (at level 0, Γ, l, t, u, A, VΓ at level 50).
Notation "[ Γ ||-v t ⤳* u : A | VΓ ]"      := (redValidity Γ _ t u A VΓ) (at level 0, Γ, t, u, A, VΓ at level 50).

Lemma validTm_return  `{GenericTypingProperties} {Γ Γ' l t u A B}
  {VΓ : [VR| ||-v Γ ≅ Γ']} {VA : [Γ ||-vS< l > A ≅ B | VΓ]}:
  [ Γ ||-vS< l > t ≅ u : A | VΓ | VA ] -> [ Γ ||-v< l > t ≅ u : A | VΓ | validTy_return VA ].
Proof.
  intros vtu.
  constructor.
  intros.
  unshelve eapply irrLR, Wpack_return', vtu; tea.
  now eapply WAd_return, VA.
Qed.



Section Inductions.
  Context `{ta : tag} `{WfContext ta} `{WfType ta} `{Typing ta}
  `{ConvType ta} `{ConvTerm ta} `{ConvNeuConv ta} `{RedType ta} `{RedTerm ta}.

  Theorem VR_rect
    (P : forall {Γ Γ' vSubstExt}, VR Γ Γ' vSubstExt -> Type)
    (hε : P VREmpty)
    (hsnocε : forall {L L' : list Fcontext} (Γ:= fromFctx L) (Γ' := fromFctx L') {F F' VΓ VΓad VF},
      P VΓad -> P (VRSnocε (L := L) (L':=L') (F := F) (F':=F') VΓ VΓad VF))
    (hsnoc : forall {Γ Γ' A A' l VΓ VΓad VA},
      P VΓad -> P (VRSnoc (Γ := Γ) (Γ':=Γ') (A := A) (A':=A') (l := l) VΓ VΓad VA)) :
    forall {Γ Γ' : context} {vSubstExt} (VΓ : VR Γ Γ' vSubstExt), P VΓ.
  Proof.
    fix ih 4; destruct VΓ; [apply hε | apply hsnocε; apply ih | apply hsnoc; apply ih].
  Defined.

  Theorem validity_rect
    (P : forall {Γ Γ' : context}, [||-v Γ ≅ Γ'] -> Type)
    (hε : P validEmpty)
    (hsnocε : forall {L L' : list Fcontext} (Γ:= fromFctx L) (Γ' := fromFctx L') {F F'}
      (VΓ : [||-v Γ ≅ Γ']) (VF : F =ε F'), P VΓ -> P (validSnocε VΓ VF))
    (hsnoc : forall {Γ Γ' : context}  {A A' l} (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v< l > A ≅ A' | VΓ]), P VΓ -> P (validSnoc VΓ VA)) :
    forall {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']), P VΓ.
  Proof.
    intros Γ Γ' [[eq] VΓad]; revert Γ Γ' eq VΓad.
    apply VR_rect with (P:= fun Γ Γ' eq VΓ => P Γ Γ' (Build_VAdequate (Build_VPack _ _ eq) VΓ)).
    - apply hε.
    - intros * ?? * ?. cbn in *. apply hsnocε with (1:=X).
    - intros *; apply hsnoc.
  Defined.

  Import EqNotations.



  (* Example check_uip_context : UIP context. Proof. typeclasses eauto. Qed. *)
(*   Lemma invValidity {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) :
    match Γ as Γ return forall Γ', [||-v Γ ≅ Γ'] -> Type with
    | Build_context nil L => fun Γ₀ VΓ₀ => ∑ (e : Tctx Γ₀ = nil),
        rew [fun Γ₀ => [||-v fromFctx L ≅ Γ₀]] (f_equal (fun Γ => Build_context Γ (Fctx Γ₀)) e) in VΓ₀ = validEmpty
    | Build_context (A :: Γ)%list L => fun Γ₀ VΓ₀ =>
      ∑ l A' Γ' (VΓ : [||-v Build_context Γ L ≅ Γ']) (VA : [Build_context Γ L ||-v< l > A ≅ A' | VΓ]) (e : Tctx Γ₀ = Tctx (Γ' ,, A')) (eF : Fctx Γ₀ = Fctx (Γ' ,, A')),
        rew [fun Γ₀ => [||-v (Build_context Γ L),,A ≅ Γ₀]] ((f_equal2 Build_context e eF)) in VΓ₀ = validSnoc VΓ VA
    end Γ' VΓ.
  Proof.
    pattern Γ, Γ', VΓ; apply validity_rect; intros.
    - exists eq_refl; reflexivity.
    - do 5 eexists; do 2 exists eq_refl; reflexivity.
  Defined. *)

  (* Example check_uip_context : UIP context. Proof. typeclasses eauto. Qed. *)
  Lemma invValidity {Γ Γ' : context} (VΓ : [||-v Γ ≅ Γ']) :
    match Γ as Γ return forall Γ', [||-v Γ ≅ Γ'] -> Type with
    | Build_context nil nil => fun Γ₀ VΓ₀ => ∑ (e : Γ₀ = ε),
        rew [fun Γ₀ => [||-v ε ≅ Γ₀]] e in VΓ₀ = validEmpty
    | Build_context nil (F :: L)%list => fun Γ₀ VΓ₀ =>
      ∑ F' L' (VΓ : [||-v fromFctx L ≅ fromFctx L']) (VF : F =ε F') (e : Γ₀ = (fromFctx L' ,, ↦ F')),
        rew [fun Γ₀ => [||-v (fromFctx L),,↦ F ≅ Γ₀]] e in VΓ₀ = validSnocε VΓ VF
    | Build_context (A :: Γ)%list L => fun Γ₀ VΓ₀ =>
      ∑ l A' Γ' (VΓ : [||-v Build_context Γ L ≅ Γ']) (VA : [Build_context Γ L ||-v< l > A ≅ A' | VΓ]) (e : Γ₀ = (Γ' ,, A')),
        rew [fun Γ₀ => [||-v (Build_context Γ L),,A ≅ Γ₀]] e in VΓ₀ = validSnoc VΓ VA
    end Γ' VΓ.
  Proof.
    pattern Γ, Γ', VΓ; apply validity_rect; intros.
    - exists eq_refl; reflexivity.
    - do 4 eexists; exists eq_refl; reflexivity.
    - do 5 eexists; exists eq_refl; reflexivity.
  Defined.

  Lemma invValidityEmpty (VΓ : [||-v ε ≅ ε]) : VΓ = validEmpty.
  Proof.
    destruct (invValidity VΓ) as (e&h).
    now rewrite (uip e eq_refl) in h.
  Qed.

  Lemma invValiditySnocε {L L' F F'} (VΓ₀ : [||-v fromFctx L,,↦ F ≅ fromFctx L',,↦ F']) :
    ∑ (VΓ : [||-v fromFctx L ≅ fromFctx L']) (VF : F =ε F') , VΓ₀ = validSnocε VΓ VF.
  Proof.
    destruct (invValidity VΓ₀) as (F''&L''&VΓ&VF&e&h); cbn in *.
    pose proof (f_equal Fctx e) as e'; cbn in e'.
    inversion e'; subst.
    rewrite (uip e eq_refl) in h.
    now do 2 eexists.
  Qed.

  Lemma invValiditySnoc {Γ Γ' A A'} (VΓ₀ : [||-v Γ ,, A ≅ Γ',, A' ]) :
      ∑ l (VΓ : [||-v Γ ≅ Γ']) (VA : [Γ ||-v< l > A ≅ A'| VΓ]), VΓ₀ = validSnoc VΓ VA.
  Proof.
    destruct (invValidity VΓ₀) as (l&A''&Γ''&VΓ&VA&e&h).
    destruct Γ' as [Γ' L'], Γ'' as [Γ'' L'']; cbn in *; subst.
    pose proof (f_equal Fctx e) as e'; cbn in e'; destruct e'.
    pose proof (f_equal Tctx e) as e'; cbn in e'.
    inversion e'; subst.
    rewrite (uip e eq_refl) in h.
    now do 3 eexists.
  Qed.

End Inductions.

(* Unhappy about the naming of inductive hyps with induction Γ, Γ', VΓ using validity_rect *)
(* the tactic indValid VΓ expects an identifier VΓ: [||-v Γ ≅ Γ'] and applies the induction principle *)
Ltac indValid VΓ :=
  match type of VΓ with
  | [||-v ?Γ ≅ ?Γ' ] =>
    pattern Γ, Γ', VΓ; apply validity_rect; clear Γ Γ' VΓ
  end.


(* Tactics to instantiate validity proofs in the context with
  valid substitions *)

Definition wfCtxOfsubstS `{GenericTypingProperties}
  {Γ Γ' Δ : context} {wfΔ : [|- Δ]} {σ σ'} {VΓ : [||-v Γ ≅ Γ']}  :
  [Δ ||-v σ ≅ σ' : Γ | VΓ | wfΔ] -> [|- Δ] := fun _ => wfΔ.

Ltac instValid vσ :=
  let wfΔ := (eval unfold wfCtxOfsubstS in (wfCtxOfsubstS vσ)) in
  repeat lazymatch goal with
  | [H : typeValidity _ _ _ _ _ _ |- _] =>
    try (let X := fresh "R" H in pose (X := validTyExt H wfΔ vσ)) ;
     (* TODO: should only do that if vσ : [.. |- σ ≅ σ' : ...] with σ != σ' *)
    try (let X := fresh "Rl" H in pose (X := validTyExt H wfΔ (lrefl vσ))) ;
    try (let X := fresh "Rr" H in pose (X := validTyExt H wfΔ (urefl vσ))) ;
    block H
  | [H : termEqValidity _ _ _ _ _ _ _ _ _ |- _] =>
    try (let X := fresh "R" H in pose (X := validTmExt H wfΔ vσ)) ;
    try (let X := fresh "Rl" H in pose (X := validTmExt H wfΔ (lrefl vσ))) ;
    try (let X := fresh "Rr" H in pose (X := validTmExt H wfΔ (urefl vσ))) ;
    block H
  end; unblock.

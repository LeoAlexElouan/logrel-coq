(** * LogRel.GenericTyping: the generic interface of typing used to build the logical relation. *)
From Stdlib Require Import CRelationClasses ssrbool.
From LogRel Require Import Utils Syntax.All.

(** In order to factor the work, the logical relation is defined over a generic
notion of typing (and conversion),
and its properties are established given abstract properties
of this generic notion. This way, we can instantiate the logical relation multiple
times with different instances of this abstract notion of typing, gathering more
and more properties. *)

(**
More precisely, an instance consists of giving notions of
- context well-formation [|- Γ]
- type well-formation [Γ |- A]
- term well-formation [Γ |- t : A]
- convertibility of types [Γ |- A ≅ B]
- convertibility of terms [Γ |- t ≅ u : A]
- neutral convertibility of terms [Γ |- m ~ n : A]
- (multi-step, weak-head) reduction of types [Γ |- A ⤳* B]
- (multi-step, weak-head) reduction of terms [Γ |- t ⤳* u : A]
*)


(** ** Generic definitions *)

(** These can be defined over typing and conversion in a generic way. *)

Section RedDefinitions.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  (** *** Bundling of a predicate with side-conditions *)

  Record TypeConvWf (Γ : context) (A B : term) : Type :=
    {
      tyc_wf_l : [Γ |- A] ;
      tyc_wf_r : [Γ |- B] ;
      tyc_wf_conv :> [Γ |- A ≅ B]
    }.

  Record TermConvWf (Γ : context) (A t u : term) : Type :=
    {
      tmc_wf_l : [Γ |- t : A] ;
      tmc_wf_r : [Γ |- u : A] ;
      tmc_wf_conv :> [Γ |- t ≅ u : A]
    }.

  Record TypeRedWf {Γ : context} {A B : term} : Type := {
    tyr_wf_r : [Γ |- B];
    tyr_wf_red :> [Γ |- A ⤳* B]
  }.

  Record TermRedWf {Γ : context} {A t u : term} : Type := {
    tmr_wf_r : [Γ |- u : A];
    tmr_wf_red :> [Γ |- t ⤳* u : A]
  }.

  Record TypeRedWhnf {Γ : context} {A : term} : Type :=
    {
      tyred_whnf : term ;
      tyred_whnf_red :> @TypeRedWf Γ A tyred_whnf ;
      tyred_whnf_isType :> isType tyred_whnf
    }.


  Record TermRedWhnf {Γ : context} {A t : term} : Type :=
    {
      tmred_whnf : term ;
      tmred_whnf_red :> @TermRedWf Γ A t tmred_whnf ;
      tmred_whnf_whnf :> whnf tmred_whnf
    }.

  (** *** Lifting of typing and conversion to contexts and substitutions *)

  Inductive WellSubst (Γ : context) : context -> substitution -> Type :=
    | well_sempty (σ : substitution) : [Γ |-s σ : ε]
    | well_sconsε (σ : substitution) L F : [Γ |-s εtail_subst σ : fromFctx L] ->
      [Γ |-s σ : fromFctx L,, ↦ F]
    | well_scons (σ : substitution) (Δ : context) A :
      [Γ |-s tail_subst σ : Δ] -> [Γ |- subst_subst σ var_zero : A[tail_subst σ]] ->
      [Γ |-s σ : Δ,, A]
  where "[ Γ '|-s' σ : Δ ]" := (WellSubst Γ Δ σ).

  Inductive ConvSubst (Γ : context) : context -> substitution -> substitution -> Type :=
  | conv_sempty (σ τ : substitution) : [Γ |-s σ ≅ τ : ε ]
  | conv_sconsε (σ τ: substitution) L F : [Γ |-s εtail_subst σ ≅ εtail_subst τ : fromFctx L] ->
      [Γ |-s σ ≅ τ: fromFctx L,, ↦ F]
  | conv_scons (σ τ : substitution) (Δ : context) A :
    [Γ |-s tail_subst σ ≅ tail_subst τ : Δ] -> [Γ |- subst_subst σ var_zero ≅ subst_subst τ var_zero: A[tail_subst σ]] ->
    [Γ |-s σ ≅ τ : Δ,,A ]
  where "[ Γ '|-s' σ ≅ τ : Δ ]" := (ConvSubst Γ Δ σ τ).

(*   Inductive ConvCtx : context -> context -> Type :=
  | conv_cempty: [ ε ≅ ε ]
  | conv_cconsε L F L' F' : [ fromFctx L ≅ fromFctx L' ] -> F =ε F' -> [ fromFctx L,,↦ F ≅ fromFctx L',,↦ F' ]
  | conv_ccons Γ A Δ B : [ Γ ≅ Δ ] -> [Γ |- A ≅ B] -> [ Γ,,A ≅ Δ,,B ]
  where "[ Γ ≅ Δ ]" := (ConvCtx Γ Δ). *)


(*   Lemma well_subst_ext Γ Δ (σ σ' : substitution) :
    σ =1 σ' ->
    [Γ |-s σ : Δ] ->
    [Γ |-s σ' : Δ].
  Proof.
    intros Heq.
    induction 1 in σ', Heq |- *.
    all: constructor.
    - eapply IHWellSubst.
      now rewrite Heq.
    - rewrite <- Heq.
      now replace A[↑ >> σ'] with A[↑ >> σ]
        by (now rewrite Heq).
  Qed. *)

  Definition WellClass (Γ : context) (A : class) (t : term) :=
    match A with
      | istype => [Γ |- t]
      | isterm A => [Γ |- t : A]
    end.

  Definition term_class_ty Γ (A : term) t :
    [Γ |- t : A] -> WellClass Γ (isterm A) t :=
    fun H => H.

  Definition type_class_ty Γ A :
    [Γ |- A] -> WellClass Γ istype A :=
    fun H => H.

  Record well_typed Γ t :=
  {
    well_typed_type : term ;
    well_typed_typed : [Γ |- t : well_typed_type]
  }.

  Record well_formed Γ t :=
  {
    well_formed_class : class ;
    well_formed_typed : WellClass Γ well_formed_class t
  }.

  Definition ConvClass (Γ : context) (A : class) (t u : term) :=
    match A with
      | istype => [Γ |- t ≅ u]
      | isterm A => [Γ |- t ≅ u : A]
    end.

  Record RedClosureClass (Γ : context) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |- t] | isterm A => [Γ |- t : A] end;
    reddecl_red : @RedClosureAlg Γ t u;
    reddecl_conv : ConvClass Γ A t u ;
  }.

  Inductive isWfFun (Γ : context) (A B : term) : term -> Set :=
    LamWfFun : forall A' t : term,
      [Γ |- A'] -> [Γ |- A ≅ A'] -> [Γ,, A |- t : B] (*-> [Γ,, A' |- t : B] *) -> isWfFun Γ A B (tLambda A' t)
  | AlphaWfFun : forall i, [Γ |- tProd A B ≅ arr' Γ tNat tBool ] -> isWfFun Γ A B (tAlpha i)
  | EvalWfFun : forall ℓ v, [Γ |- tProd A B ≅ arr' Γ tNat tBool ] -> isWfFun Γ A B (tEval ℓ (tRel v))
  | NeWfFun : forall f : term, [Γ |- f ~ f : tProd A B] -> isWfFun Γ A B f.

  Inductive isWfPair (Γ : context) (A B : term) : term -> Set :=
    PairWfPair : forall A' B' a b : term,
      [Γ |- A'] ->
      [Γ |- A ≅ A'] ->
      [Γ |- a : A] ->
      [Γ |- B[a..]] ->
      [Γ |- B'[a..]] ->
      [Γ |- B[a..] ≅ B'[a..]] ->
      [Γ |- b : term_decl B[a..]] ->
      isWfPair Γ A B (tPair A' B' a b)
  | NeWfPair : forall n : term, [Γ |- n ~ n : tSig A B] -> isWfPair Γ A B n.

End RedDefinitions.

Arguments TypeRedWf : clear implicits.
Arguments TypeRedWf {_ _ _}.
Arguments TermRedWf : clear implicits.
Arguments TermRedWf {_ _ _}.
Arguments TypeRedWhnf : clear implicits.
Arguments TypeRedWhnf {_ _ _}.
Arguments TermRedWhnf : clear implicits.
Arguments TermRedWhnf {_ _ _}.


Notation "[ Γ |- A ↘ ]" := (TypeRedWhnf Γ A) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A ↘ ]" := (TypeRedWhnf (ta := ta) Γ A) : typing_scope.
Notation "[ Γ |- t ↘ A ]" := (TermRedWhnf Γ A t) (only parsing ): typing_scope.
Notation "[ Γ |-[ ta  ] t ↘ A ]" := (TermRedWhnf (ta := ta) Γ A t) : typing_scope.
Notation "[ Γ |- A :≅: B ]" := (TypeConvWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :≅: B ]" := (TypeConvWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :≅: u : A ]" := (TermConvWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :≅: u : A ]" := (TermConvWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ |- A :⤳*: B ]" := (TypeRedWf Γ A B) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] A :⤳*: B ]" := (TypeRedWf (ta := ta) Γ A B) : typing_scope.
Notation "[ Γ |- t :⤳*: u : A ]" := (TermRedWf Γ A t u) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta  ] t :⤳*: u : A ]" := (TermRedWf (ta := ta) Γ A t u) : typing_scope.
Notation "[ Γ '|-s' σ : A ]" := (WellSubst Γ A σ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ : A ]" := (WellSubst (ta := ta) Γ A σ) : typing_scope.
Notation "[ Γ '|-s' σ ≅ τ : A ]" := (ConvSubst Γ A σ τ) (only parsing) : typing_scope.
Notation "[ Γ |-[ ta ']s' σ ≅ τ : A ]" := (ConvSubst (ta := ta) Γ A σ τ) : typing_scope.
(* Notation "[ L | Γ ≅ Δ ]" := (ConvCtx L Γ Δ) (only parsing) : typing_scope. *)
(* Notation "[ L |[ ta  ] Γ ≅ Δ ]" := (ConvCtx (ta := ta) L Γ Δ) : typing_scope. *)
Notation "[ Γ |- t ∈ A ]" := (WellClass Γ A t) : typing_scope.
Notation "[ Γ |-[ ta  ] t ∈ A ]" := (WellClass (ta := ta) Γ A t) : typing_scope.
Notation "[ Γ |- t ≅ t' ∈ A ]" := (ConvClass Γ A t t') : typing_scope.
Notation "[ Γ |-[ ta  ] t ≅ t' ∈ A ]" := (ConvClass (ta := ta) Γ A t t') : typing_scope.

#[export] Hint Resolve
  Build_TypeRedWhnf Build_TermRedWhnf Build_TypeConvWf
  Build_TermConvWf Build_TypeRedWf Build_TermRedWf
  well_sempty well_scons conv_sempty conv_scons
  tyr_wf_r tyr_wf_red tmr_wf_r tmr_wf_red
  : gen_typing.

#[export] Hint Extern 1 =>
  now unshelve first [ eapply tyred_whnf_red|eapply tmred_whnf_red
    | eapply tyred_whnf_isType| eapply tmred_whnf_whnf] : gen_typing.

(** ** Properties of the abstract interface *)

Section GenericTyping.

  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta} `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

  Class WfContextProperties :=
  {
    wfc_nil : [|- ε ] ;
    wfc_cons {Γ} {A} : [|- Γ] -> [Γ |- A] -> [|- Γ,,A];
    wfc_consF {Γ} {i new} {b} : [|- Γ] -> [|- Γ,, i : new ↦ b];
    wfc_alpha {Γ} : [|- Γ] -> [|- Γ,, ↦ nil_ell];
    wfc_wft {Γ A} : [Γ |- A] -> [|- Γ];
    wfc_ty {Γ A t} : [Γ |- t : A] -> [|- Γ];
    wfc_convty {Γ A B} : [Γ |- A ≅ B] -> [|- Γ];
    wfc_convtm {Γ A t u} : [Γ |- t ≅ u : A] -> [|- Γ];
    wfc_redty {Γ A B} : [Γ |- A ⤳* B] -> [|- Γ];
    wfc_redtm {Γ A t u} : [Γ |- t ⤳* u : A] -> [|- Γ];
  }.

  Class WfTypeProperties :=
  {
    wft_wk {Γ Δ A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A] -> [Δ |- A⟨ρ⟩] ;
    wft_U {Γ} :
      [ |- Γ ] ->
      [ Γ |- U ] ;
    wft_prod {Γ} {A B} :
      [ Γ |- A ] ->
      [Γ ,, A |- B ] ->
      [ Γ |- tProd A B ] ;
    wft_sig {Γ} {A B} :
      [ Γ |- A ] ->
      [Γ ,, A |- B ] ->
      [ Γ |- tSig A B ] ;
    wft_Id {Γ} {A x y} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- y : A] ->
      [Γ |- tId A x y] ;
    wft_term {Γ} {A} :
      [ Γ |- A : U ] ->
      [ Γ |- A ] ;
    wft_split {Γ A i new} :
      [|- Γ] ->
      [ Γ,, i : new ↦ true |- A] ->
      [ Γ,, i : new ↦ false |- A] ->
      [ Γ |- A] ;
  }.

  Class TypingProperties :=
  {
    ty_wk {Γ Δ t A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t : A] -> [Δ |- t⟨ρ⟩ : A⟨ρ⟩] ;
    ty_var {Γ} {n decl} :
      [   |- Γ ] ->
      in_ctx Γ n decl ->
      [ Γ |- tRel n : decl ] ;
    ty_prod {Γ} {A B} :
        [ Γ |- A : U] ->
        [Γ ,, A |- B : U ] ->
        [ Γ |- tProd A B : U ] ;
    ty_lam {Γ}  {A B t : term} :
        [ Γ |- A ] ->
        [ Γ ,, A |- t : B ] ->
        [ Γ |- tLambda A t : tProd A B] ;
    ty_app {Γ}  {f a A B} :
        [ Γ |- f : tProd A B ] ->
        [ Γ |- a : A ] ->
        [ Γ |- tApp f a : term_decl B[a ..] ] ;
    ty_nat {Γ} :
        [|-Γ] ->
        [Γ |- tNat : U] ;
    ty_zero {Γ} :
        [|-Γ] ->
        [Γ |- tZero : tNat] ;
    ty_succ {Γ n} :
        [Γ |- n : tNat] ->
        [Γ |- tSucc n : tNat] ;
    ty_natElim {Γ P hz hs n} :
      [Γ ,, tNat |- P ] ->
      [Γ |- hz : term_decl P[tZero..]] ->
      [Γ |- hs : elimSuccHypTy' Γ P] ->
      [Γ |- n : tNat] ->
      [Γ |- tNatElim P hz hs n : term_decl P[n..]] ;
    ty_bool {Γ} :
        [|-Γ] ->
        [Γ |- tBool : U] ;
    ty_true {Γ} :
        [|-Γ] ->
        [Γ |- tTrue : tBool] ;
    ty_false {Γ} :
        [|-Γ] ->
        [Γ |- tFalse : tBool] ;
    ty_boolElim {Γ P ht hf n} :
      [Γ ,, tBool |- P ] ->
      [Γ |- ht : term_decl P[tTrue..]] ->
      [Γ |- hf : term_decl P[tFalse..]] ->
      [Γ |- n : tBool] ->
      [Γ |- tBoolElim P ht hf n : term_decl P[n..]] ;
    ty_alpha {Γ : context} {i : list_index Γ} :
      [|- Γ] ->
      [Γ |- tAlpha i : arr' Γ tNat tBool];
    ty_empty {Γ} :
        [|-Γ] ->
        [Γ |- tEmpty : U] ;
    ty_emptyElim {Γ P e} :
      [Γ ,,  tEmpty |- P ] ->
      [Γ |- e : tEmpty] ->
      [Γ |- tEmptyElim P e : term_decl P[e..]] ;
    ty_tree {Γ} :
        [|-Γ] ->
        [Γ |- tTree : U] ;
    ty_leaf {Γ n} :
        [Γ|- n : tNat] ->
        [Γ |- tLeaf n : tTree] ;
    ty_node {Γ n tl tr} :
        [Γ |- n : tNat] ->
        [Γ |- tl : tTree] ->
        [Γ |- tr : tTree] ->
        [Γ |- tNode n tl tr : tTree] ;
    ty_treeElim {Γ P hl hn t} :
      [Γ ,, tTree |- P ] ->
      [Γ |- hl : elimLeafHypTy' Γ P] ->
      [Γ |- hn : elimNodeHypTy' Γ P] ->
      [Γ |- t : tTree] ->
      [Γ |- tTreeElim P hl hn t : term_decl P[t..]] ;
    ty_sig {Γ} {A B} :
        [ Γ |- A : U] ->
        [Γ ,, A |- B : U ] ->
        [ Γ |- tSig A B : U ] ;
    ty_pair {Γ} {A B a b} :
        [ Γ |- A ] ->
        [Γ ,, A |- B ] ->
        [Γ |- a : A] ->
        [Γ |- b : term_decl B[a..]] ->
        [Γ |- tPair A B a b : tSig A B] ;
    ty_fst {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tFst p : A] ;
    ty_snd {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tSnd p : term_decl B[(tFst p)..]] ;
    ty_Id {Γ} {A x y} :
      [Γ |- A : U] ->
      [Γ |- x : A] ->
      [Γ |- y : A] ->
      [Γ |- tId A x y : U] ;
    ty_refl {Γ A x} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- tRefl A x : tId A x x] ;
    ty_IdElim {Γ A x P hr y e} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : term_decl P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- e : tId A x y] ->
      [Γ |- tIdElim A x P hr y e : term_decl P[e .: y..]];
    ty_exp {Γ} {t A A' : term} : 
      [Γ |- t : A'] ->
      [Γ |- A ⤳* A'] ->
      [Γ |- t : A] ;
    ty_conv {Γ} {t A A' : term} : 
      [Γ |- t : A'] -> 
      [Γ |- A' ≅ A] -> 
      [Γ |- t : A] ;
    ty_split {Γ t A i ne} :
      [|- Γ] ->
      [ Γ,, i : ne ↦ true |- t : A] ->
      [ Γ,, i : ne ↦ false |- t : A] ->
      [ Γ |- t : A] ;
    ty_xi  {Γ t} {ℓ : ell} :
      [|- Γ] ->
      [ Γ ,, ℓ |- t : tNat] ->
      [ Γ |- tXi ℓ t : tTree] ;
    ty_xxi {Γ t u} {ℓ : ell} :
      [ |- Γ] ->
      [ Γ ,, ℓ |- t : tNat] -> [ Γ |- u : ℓ] ->
      [ Γ |- tXXi ℓ t u : tId tNat (dEval' Γ (tXi ℓ t) (tEval ℓ u)) t[u..] ] ;
    ty_eval {Γ t} {ℓ : ell} :
      [ Γ |- t : ℓ ] ->
      [ Γ |- tEval ℓ t : arr' Γ tNat tBool] ;
    ty_box {Γ t} {ℓ : ell} :
      [ Γ |- t : arr' Γ tNat tBool] ->
      (forall n b, in_ell ℓ n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
      [ Γ |- tBox ℓ t : ℓ] ;
    ty_ellElim {Γ ℓ k P ht hf n b} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      [ Γ,, ℓ |- P] ->
      [ Γ,, ℓt |- ht : term_decl P[tBox ℓ (tEval ℓt (tRel 0))]⇑ ] ->
      [ Γ,, ℓf |- hf : term_decl P[tBox ℓ (tEval ℓf (tRel 0))]⇑ ] ->
      [ Γ |- n : ℓ] -> [Γ |- b : tBool] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
      [ Γ |- tEllElim k ℓ P ht hf n b : term_decl P[n..] ] ;
  }.

  Class ConvTypeProperties :=
  {
    convty_term {Γ A B} : [Γ |- A ≅ B : U] -> [Γ |- A ≅ B] ;
    convty_equiv {Γ} :: PER (conv_type Γ) ;
    convty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ≅ B] -> [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩] ;
    convty_exp {Γ A A' B B'} :
      [Γ |- A ⤳* A'] -> [Γ |- B ⤳* B'] ->
      [Γ |- A' ≅ B'] -> [Γ |- A ≅ B] ;
    convty_uni {Γ} :
      [|- Γ] -> [Γ |- U ≅ U] ;
    convty_prod {Γ A A' B B'} :
      [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] ->
      [Γ |- tProd A B ≅ tProd A' B'] ;
    convty_sig {Γ A A' B B'} :
      [Γ |- A] ->
      [Γ |- A ≅ A'] -> [Γ,, A |- B ≅ B'] ->
      [Γ |- tSig A B ≅ tSig A' B'] ;
    convty_Id {Γ A A' x x' y y'} :
      (* [Γ |- A] -> ?  *)
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- tId A x y ≅ tId A' x' y' ] ;
    convty_split {Γ A A' i new} :
      [|- Γ] ->
      [ Γ,, i : new ↦ true |- A ≅ A'] ->
      [ Γ,, i : new ↦ false |- A ≅ A'] ->
      [ Γ |- A ≅ A'] ;
  }.

  Class ConvTermProperties :=
  {
    convtm_equiv {Γ A} :: PER (conv_term Γ A) ;
    convtm_conv {Γ} {t u A A' : term} : [Γ |- t ≅ u : A] -> [Γ |- A ≅ A'] -> [Γ |- t ≅ u : A'] ;
    convtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ≅ u : A] -> [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩] ;
    convtm_exp {Γ A t t' u u'} :
      [Γ |- t ⤳* t' : A] -> [Γ |- u ⤳* u' : A] ->
      [Γ |- A] -> [Γ |- t' : A] -> [Γ |- u' : A] ->
      [Γ |- A ≅ A] -> [Γ |- t' ≅ u' : A] -> [Γ |- t ≅ u : A] ;
    convtm_convneu {Γ n n' A} :
      isPosType A ->
      [Γ |- n ~ n' : A  ] -> [Γ |- n ≅ n' : A] ;
    convtm_prod {Γ A A' B B'} :
      [Γ |- A : U] ->
      [Γ |- A ≅ A' : U] -> [Γ,, A |- B ≅ B' : U] ->
      [Γ |- tProd A B ≅ tProd A' B' : U] ;
    convtm_sig {Γ A A' B B'} :
      [Γ |- A : U] ->
      [Γ |- A ≅ A' : U] -> [Γ,, A |- B ≅ B' : U] ->
      [Γ |- tSig A B ≅ tSig A' B' : U] ;
    convtm_eta {Γ f g A B} :
      [ Γ |- A ] ->
      [ Γ,, A |- B ] ->
      [ Γ |- f : tProd A B ] ->
      isWfFun Γ A B f ->
      [ Γ |- g : tProd A B ] ->
      isWfFun Γ A B g ->
      [ Γ ,, A |- eta_expand' Γ A f ≅ eta_expand' Γ A g : B ] ->
      [ Γ |- f ≅ g : tProd A B ] ;
    convtm_nat {Γ} :
      [|-Γ] -> [Γ |- tNat ≅ tNat : U] ;
    convtm_zero {Γ} :
      [|-Γ] -> [Γ |- tZero ≅ tZero : tNat] ;
    convtm_succ {Γ} {n n'} :
        [Γ |- n ≅ n' : tNat] ->
        [Γ |- tSucc n ≅ tSucc n' : tNat] ;
    convtm_bool {Γ} :
      [|-Γ] -> [Γ |- tBool ≅ tBool : U] ;
    convtm_true {Γ} :
      [|-Γ] -> [Γ |- tTrue ≅ tTrue : tBool] ;
    convtm_false {Γ} :
      [|-Γ] -> [Γ |- tFalse ≅ tFalse : tBool] ;
    convtm_alpha {Γ : context} {i : list_index Γ} :
      [|-Γ] -> [Γ |- tAlpha i ≅ tAlpha i : arr' Γ tNat tBool] ;
    convtm_digamma {Γ i n b} :
      [|-Γ] ->
      in_ell (list_at Γ i) n b -> [Γ |- tApp (tAlpha i) (nat_to_term n) ≅ bool_to_term b : tBool] ;
    convtm_empty {Γ} :
      [|-Γ] -> [Γ |- tEmpty ≅ tEmpty : U] ;
    convtm_tree {Γ} :
      [|-Γ] -> [Γ |- tTree ≅ tTree : U] ;
    convtm_leaf {Γ n n'} :
      [Γ |- n ≅ n': tNat] -> [Γ |- tLeaf n ≅ tLeaf n': tTree] ;
    convtm_node {Γ} {n n' tl tl' tr tr'} :
        [Γ |- n ≅ n' : tNat] ->
        [Γ |- tl ≅ tl' : tTree] ->
        [Γ |- tr ≅ tr' : tTree] ->
        [Γ |- tNode n tl tr ≅ tNode n' tl' tr' : tTree] ;
    convtm_eta_sig {Γ p p' A B} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- p : tSig A B] ->
      isWfPair Γ A B p ->
      [Γ |- p' : tSig A B] ->
      isWfPair Γ A B p' ->
      [Γ |- tFst p ≅ tFst p' : A] ->
      [Γ |- tSnd p ≅ tSnd p' : term_decl B[(tFst p)..]] ->
      [Γ |- p ≅ p' : tSig A B] ;
    convtm_Id {Γ A A' x x' y y'} :
      (* [Γ |- A] -> ?  *)
      [Γ |- A ≅ A' : U] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- tId A x y ≅ tId A' x' y' : U ] ;
    convtm_refl {Γ A A' x x'} :
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ |- tRefl A x ≅ tRefl A' x' : tId A x x] ;
    convtm_split {Γ t u A i new} :
      [|- Γ] ->
      [ Γ,, i : new ↦ true |- t ≅ u : A] ->
      [ Γ,, i : new ↦ false |- t ≅ u : A] ->
      [ Γ |- t ≅ u :A] ;
    convtm_xi {Γ t t'} {ℓ : ell} :
      [ |- Γ] ->
      [ Γ ,, ℓ |- t ≅ t' : tNat] ->
      [ Γ |- tXi ℓ t ≅ tXi ℓ t' : tTree] ;
    convtm_xxi {Γ t t' u u'} {ℓ : ell} :
      [ |- Γ] ->
      [ Γ ,, ℓ |- t ≅ t' : tNat] -> [ Γ |- u ≅ u' : ℓ] ->
      [ Γ |- tXXi ℓ t u ≅ tXXi ℓ t' u' : tId tNat (dEval' Γ (tXi ℓ t) (tEval ℓ u)) t[u..] ] ;
    convtm_evalCong {Γ t t'} {ℓ : ell} :
          [ Γ |- t ≅ t' : ℓ ] ->
          [ Γ |- tEval ℓ t ≅ tEval ℓ t' : arr' Γ tNat tBool] ;
    convtm_box {Γ t t'} {ℓ : ell} :
      [ Γ |- t ≅ t' : arr' Γ tNat tBool] ->
      (forall n b, in_ell ℓ n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
      [ Γ |- tBox ℓ t ≅ tBox ℓ t' : ℓ] ;
  }.

  Class ConvNeuProperties :=
  {
    convneu_equiv {Γ A} :: PER (conv_neu_ty Γ A) ;
    convneu_conv {Γ} {t u A A' : term} : [Γ |- t ~ u : A  ] -> [Γ |- A ≅ A'] -> [Γ |- t ~ u : A'  ] ;
    convneu_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ~ u : A  ] -> [Δ |- t⟨ρ⟩ ~ u⟨ρ⟩ : A⟨ρ⟩ ] ;
    convneu_whne {Γ A t u} : [Γ |- t ~ u : A  ] -> whne t;
    convneu_var {Γ n A} :
      [Γ |- tRel n : A] -> [Γ |- tRel n ~ tRel n : A] ;
    convneu_evalrel {Γ} {ℓ : ell} {v} {k : newnat ℓ} : [Γ |- tRel v : ell_decl ℓ] ->
      [Γ |- tApp (tEval ℓ (tRel v)) (nat_to_term k) ~
      tApp (tEval ℓ (tRel v)) (nat_to_term k) : tBool];
    convneu_app {Γ f g t u A B} :
      [ Γ |- f ~ g : tProd A B  ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ~ tApp g u : term_decl B[t..]  ] ;
    convneu_natElim {Γ P P' hz hz' hs hs' n n'} :
        [Γ ,, tNat |- P ≅ P'] ->
        [Γ |- hz ≅ hz' : term_decl P[tZero..]] ->
        [Γ |- hs ≅ hs' : elimSuccHypTy' Γ P] ->
        [Γ |- n ~ n' : tNat ] ->
        [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' : term_decl P[n..] ] ;
    convneu_boolElim {Γ P P' ht ht' hf hf' n n'} :
        [Γ ,, tBool |- P ≅ P'] ->
        [Γ |- ht ≅ ht' : term_decl P[tTrue..]] ->
        [Γ |- hf ≅ hf' : term_decl P[tFalse..]] ->
        [Γ |- n ~ n' : tBool ] ->
        [Γ |- tBoolElim P ht hf n ~ tBoolElim P' ht' hf' n' : term_decl P[n..] ] ;
    convneu_alpha {Γ : context} {i : list_index Γ} {t u n} :
      [ Γ |- t ~ u : tNat  ] ->
      [ Γ |- tApp (tAlpha i) (nSucc n t) ~ tApp (tAlpha i) (nSucc n u) : tBool  ];
    convneu_emptyElim {Γ P P' e e'} :
        [Γ ,, tEmpty |- P ≅ P'] ->
        [Γ |- e ~ e' : tEmpty  ] ->
        [Γ |- tEmptyElim P e ~ tEmptyElim P' e' : term_decl P[e..]  ] ;
    convneu_treeElim {Γ P P' hl hl' hn hn' t t'} :
        [Γ ,, tTree |- P ≅ P'] ->
        [Γ |- hl ≅ hl' : elimLeafHypTy' Γ P] ->
        [Γ |- hn ≅ hn' : elimNodeHypTy' Γ P] ->
        [Γ |- t ~ t' : tTree  ] ->
        [Γ |- tTreeElim P hl hn t ~ tTreeElim P' hl' hn' t' : term_decl P[t..]  ] ;
    convneu_fst {Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B  ] ->
      [Γ |- tFst p ~ tFst p' : A  ] ;
    convneu_snd {Γ A B p p'} :
      [Γ |- p ~ p' : tSig A B  ] ->
      [Γ |- tSnd p ~ tSnd p' : term_decl B[(tFst p)..]  ] ;
    convneu_IdElim {Γ A A' x x' P P' hr hr' y y' e e'} :
      (* Parameters well formed: required by declarative instance *)
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] ->
      [Γ |- hr ≅ hr' : term_decl P[tRefl A x .: x..]] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- e ~ e' : tId A x y  ] ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : term_decl P[e .: y..]  ];
    convneu_eval {Γ t u v k} {ℓ : ell} :
      [|- Γ] -> in_ctx Γ v ℓ ->
      [ Γ |- t ~ u : tNat ] ->
      [ Γ |- tApp (tEval ℓ (tRel v)) (nSucc k t) ~ tApp (tEval ℓ (tRel v)) (nSucc k u) : tBool ];
    convneu_split {Γ t u A i new} :
      [|- Γ] ->
      [ Γ,, i : new ↦ true |- t ~ u : A  ] ->
      [ Γ,, i : new ↦ false |- t ~ u : A  ] ->
      [ Γ |- t ~ u : A  ] ;
    convneu_xi {Γ} {ℓ : ell} {m m' k v} :
      [Γ,, ℓ |- m ~ m' : tNat] -> head m = Some (k, S v) -> head m' = Some (k, S v) ->
      [Γ |- tXi ℓ (nSucc k m) ~ tXi ℓ (nSucc k m') : tTree ] ;
    convneu_xxi {ℓ : ell} {Γ m m' n n' k v} :
      [Γ |- n ≅ n' : ℓ] ->
      [Γ,, ℓ |- m ~ m' : tNat] -> head m = Some (k, S v) -> head m' = Some (k, S v) ->
      [Γ |- tXXi ℓ (nSucc k m) n ~ tXXi ℓ (nSucc k m') n' : tId tNat (dEval' Γ (tXi ℓ (nSucc k m)) (tEval ℓ n)) (nSucc k m)[n..] ] ;
    convneu_ellElim {Γ ℓ k} {P P' ht ht' hf hf' n n' b b' : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      [ Γ,, ℓ |- P ≅ P' ] ->
      [ Γ,, ℓt |- ht ≅ ht' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
      [ Γ,, ℓf |- hf ≅ hf' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
      [ Γ |- n ≅ n' : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
      [Γ |- b ~ b' : tBool ] ->
      [Γ |- tEllElim k ℓ P ht hf n b ~ tEllElim k ℓ P' ht' hf' n' b' : term_decl P[n..] ];
  }.

  Class RedTypeProperties :=
  {
    redty_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A ⤳* B] -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩] ;
    redty_sound {Γ A B} : [Γ |- A ⤳* B] -> [Γ | A ⤳* B] ;
    redty_ty_src {Γ A B} : [Γ |- A ⤳* B] -> [Γ |- A] ;
    redty_term {Γ A B} :
      [ Γ |- A ⤳* B : U] -> [Γ |- A ⤳* B ] ;
    redty_refl {Γ A} :
      [ Γ |- A] ->
      [Γ |- A ⤳* A] ;
    redty_trans {Γ} ::
      Transitive (red_ty Γ) ;
  }.

  Class RedTermProperties :=
  {
    redtm_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t ⤳* u : A] -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩] ;
    redtm_sound {Γ A t u} : [Γ |- t ⤳* u : A] -> [Γ | t ⤳* u] ;
    redtm_ty_src {Γ A t u} : [Γ |- t ⤳* u : A] -> [Γ |- t : A] ;
    redtm_beta {Γ} {A B t u : term} :
      [ Γ |- A ] ->
      [ Γ ,, A |- t : B ] ->
      [ Γ |- u : A ] ->
      [ Γ |- tApp (tLambda A t) u ⤳* t[u..] : B[u..] ] ;
    redtm_natElimZero {Γ P hz hs} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : term_decl P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy' Γ P] ->
        [Γ |- tNatElim P hz hs tZero ⤳* hz : P[tZero..]] ;
    redtm_natElimSucc {Γ P hz hs n} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : term_decl P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy' Γ P] ->
        [Γ |- n : tNat] ->
        [Γ |- tNatElim P hz hs (tSucc n) ⤳* tApp (tApp hs n) (tNatElim P hz hs n) : P[(tSucc n)..]] ;
    redtm_boolElimTrue {Γ P ht hf} :
        [Γ ,, tBool |- P ] ->
        [Γ |- ht : term_decl P[tTrue..]] ->
        [Γ |- hf : term_decl P[tFalse..]] ->
        [Γ |- tBoolElim P ht hf tTrue ⤳* ht : P[tTrue..]] ;
    redtm_boolElimFalse {Γ P ht hf} :
        [Γ ,, tBool |- P ] ->
        [Γ |- ht : term_decl P[tTrue..]] ->
        [Γ |- hf : term_decl P[tFalse..]] ->
        [Γ |- tBoolElim P ht hf tFalse ⤳* hf : P[tFalse..]] ;
    redtm_treeElimLeaf {Γ P hl hn n} :
        [Γ ,, tTree |- P ] ->
        [Γ |- hl : elimLeafHypTy' Γ P] ->
        [Γ |- hn : elimNodeHypTy' Γ P] ->
        [Γ |- n : tNat] ->
        [Γ |- tTreeElim P hl hn (tLeaf n) ⤳* tApp hl n : P[(tLeaf n)..]] ;
    redtm_treeElimNode {Γ P hl hn tl tr n} :
        [Γ ,, tTree |- P ] ->
        [Γ |- n : tNat] ->
        [Γ |- hl : elimLeafHypTy' Γ P] ->
        [Γ |- hn : elimNodeHypTy' Γ P] ->
        [Γ |- tl : tTree] ->
        [Γ |- tr : tTree] ->
        [Γ |- tTreeElim P hl hn (tNode n tl tr) ⤳*
          tApp (tApp (tApp (tApp (tApp hn n) tl) tr) (tTreeElim P hl hn tl)) (tTreeElim P hl hn tr) :
          P[(tNode n tl tr)..]] ;
    redtm_app {Γ A B f f' t} :
      [ Γ |- f ⤳* f' : tProd A B ] ->
      [ Γ |- t : A ] ->
      [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ];
    redtm_natelim {Γ P hz hs n n'} :
      [ Γ,, tNat |- P ] ->
      [ Γ |- hz : term_decl P[tZero..] ] ->
      [ Γ |- hs : elimSuccHypTy' Γ P ] ->
      [ Γ |- n ⤳* n' : tNat ] ->
      [ Γ |- tNatElim P hz hs n ⤳* tNatElim P hz hs n' : P[n..] ];
    redtm_boolelim {Γ P ht hf n n'} :
      [ Γ,, tBool |- P ] ->
      [ Γ |- ht : term_decl P[tTrue..] ] ->
      [ Γ |- hf : term_decl P[tFalse..] ] ->
      [ Γ |- n ⤳* n' : tBool ] ->
      [ Γ |- tBoolElim P ht hf n ⤳* tBoolElim P ht hf n' : P[n..] ];
    redtm_alphaSubst {Γ : context} {i : list_index Γ} {t u n} :
      [ Γ |- t ⤳* u : tNat ] ->
      [ Γ |- tApp (tAlpha i) (nSucc n t) ⤳* tApp (tAlpha i) (nSucc n u) : tBool ] ;
    redtm_alpha {Γ} {i n b} :
        [|- Γ] ->
        in_ell (list_at Γ i) n b ->[ Γ |- tApp (tAlpha i) (nat_to_term n) ⤳* bool_to_term b : tBool ] ;
    redtm_emptyelim {Γ P n n'} :
      [ Γ,, tEmpty |- P ] ->
      [ Γ |- n ⤳* n' : tEmpty ] ->
      [ Γ |- tEmptyElim P n ⤳* tEmptyElim P n' : P[n..] ];
    redtm_treeelim {Γ P hl hn t t'} :
      [ Γ,, tTree |- P ] ->
      [ Γ |- hl : elimLeafHypTy' Γ P ] ->
      [ Γ |- hn : elimNodeHypTy' Γ P ] ->
      [ Γ |- t ⤳* t' : tTree ] ->
      [ Γ |- tTreeElim P hl hn t ⤳* tTreeElim P hl hn t' : P[t..] ];
    redtm_fst_beta {Γ A B a b} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- a : A] ->
      [Γ |- b : term_decl B[a..]] ->
      [Γ |- tFst (tPair A B a b) ⤳* a : A] ;
    redtm_fst {Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B] ->
      [Γ |- tFst p ⤳* tFst p' : A] ;
    redtm_snd_beta {Γ A B a b} :
      [Γ |- A] ->
      [Γ ,, A |- B] ->
      [Γ |- a : A] ->
      [Γ |- b : term_decl B[a..]] ->
      [Γ |- tSnd (tPair A B a b) ⤳* b : B[(tFst (tPair A B a b))..]] ;
    redtm_snd {Γ A B p p'} :
      [Γ |- p ⤳* p' : tSig A B] ->
      [Γ |- tSnd p ⤳* tSnd p' : B[(tFst p)..]] ;
    redtm_idElimRefl {Γ A x P hr y A' z} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : term_decl P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- A'] ->
      [Γ |- z : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ y : A] ->
      [Γ |- x ≅ z : A] ->
      [Γ |- tIdElim A x P hr y (tRefl A' z) ⤳* hr : P[tRefl A' z .: y..]];
    redtm_idElim {Γ A x P hr y e e'} :
      [Γ |- A] ->
      [Γ |- x : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
      [Γ |- hr : term_decl P[tRefl A x .: x..]] ->
      [Γ |- y : A] ->
      [Γ |- e ⤳* e' : tId A x y] ->
      [Γ |- tIdElim A x P hr y e ⤳* tIdElim A x P hr y e' : P[e .: y..]];
    redtm_conv {Γ t u A A'} :
      [Γ |- t ⤳* u : A] ->
      [Γ |- A ≅ A'] ->
      [Γ |- t ⤳* u : A'] ;
    redtm_refl {Γ} {A t :term} :
      [ Γ |- t : A] ->
      [Γ |- t ⤳* t : A] ;
    redtm_trans {Γ A} ::
      Transitive (red_tm Γ A) ;
    redtm_xi {Γ t t' n} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t ⤳* t' : tNat] ->
          [ Γ |- tXi ℓ (nSucc n t) ⤳* tXi ℓ (nSucc n t') : tTree];
    redtm_xiLeaf {Γ n} {ℓ : ell} :
      [ |- Γ] ->
      [ Γ |- tXi ℓ (nat_to_term n) ⤳* tLeaf (nat_to_term n) : tTree];
    redtm_xiNode {Γ t} {ℓ : ell} {k} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) :
      [ |- Γ] ->
      [ Γ ,, ℓ |- t : tNat] -> whne t -> head t = Some (newnat_nat _ k, 0) ->
      [ Γ |- tXi ℓ t ⤳* tNode (nat_to_term k) (tXi ℓt t⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..])
        (tXi ℓf t⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..]) : tTree];
    redtm_xxi {Γ t t' u n} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t ⤳* t' : tNat] -> [ Γ |- u : ℓ] ->
          [ Γ |- tXXi ℓ (nSucc n t) u ⤳* tXXi ℓ (nSucc n t') u : tId tNat (dEval' Γ (tXi ℓ (nSucc n t)) (tEval ℓ u)) (nSucc n t)[u..] ] ;
    redtm_xxiLeaf {Γ n u} {ℓ : ell} :
      [ |- Γ] -> [ Γ |- u : ℓ] ->
      [ Γ |- tXXi ℓ (nat_to_term n) u ⤳* tRefl tNat (nat_to_term n): tId tNat (nat_to_term n) (nat_to_term n) ];
    redtm_xxiNode  {Γ m} {ℓ : ell} {k n} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      whne m -> head m = Some (newnat_nat _ k, 0) ->
      [ Γ,, ℓ |- m  : tNat] -> [Γ |- n : ℓ] ->
      [ Γ |- tXXi ℓ m n ⤳* tEllElim k ℓ (tId tNat (dEval' (Γ,, ℓ) (tXi ℓ m⟨wk_up ℓ (@wk1 Γ ℓ)⟩) (tEval ℓ (tRel 0))) m)
        (tXXi ℓt m⟨wk_up ℓ (@wk1 Γ ℓt)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓt) ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] (tRel 0))
        (tXXi ℓf m⟨wk_up ℓ (@wk1 Γ ℓf)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓf) ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] (tRel 0))
        n (tApp (tEval ℓ n) (nat_to_term k)):
        tId tNat (dEval' Γ (tXi ℓ m) (tEval ℓ n)) m[n..] ];
    redtm_eval {Γ v n t t'} {ℓ : ell} :
      [ Γ |- t ⤳* t' : tNat ] -> in_ctx Γ v ℓ ->
      [ Γ |- tApp (tEval ℓ (tRel v)) (nSucc n t) ⤳* tApp (tEval ℓ (tRel v)) (nSucc n t') : tBool] ;
    redtm_evalRel {Γ v n b} {ℓ : ell} :
      [ |- Γ ] ->
      in_ell ℓ n b -> in_ctx Γ v ℓ ->
      [ Γ |- tApp (tEval ℓ (tRel v)) (nat_to_term n) ⤳* (bool_to_term b) : tBool] ;
    redtm_evalBox {Γ ℓ t}:
      [ Γ |- t : arr' Γ tNat tBool] ->
      (forall n b, in_ell (ℓ : ell) n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
      [ Γ |- tEval ℓ (tBox ℓ t) ⤳* t : arr' Γ tNat tBool] ;
    redtm_ellElim {Γ ℓ k} {P ht hf n b b' : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          [ Γ,, ℓ |- P ] ->
          [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
          [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
          [ Γ |- n : ℓ] -> [Γ |- b ⤳* b' : tBool] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
          [ Γ |- tEllElim k ℓ P ht hf n b ⤳* tEllElim k ℓ P ht hf n b' : P[n..] ] ;
    redtm_ellElimTrue {Γ ℓ k} {P ht hf n : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      [ Γ,, ℓ |- P] ->
      [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
      [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
      [ Γ |- n : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ tTrue : tBool] ->
      [ Γ |- tEllElim k ℓ P ht hf n tTrue ⤳* ht[(tBox ℓt (tEval ℓ n))..] : P[n..]]; 
    redtm_ellElimFalse {Γ ℓ k} {P ht hf n : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      [ Γ,, ℓ |- P] ->
      [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
      [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
      [ Γ |- n : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ tFalse : tBool] ->
      [ Γ |- tEllElim k ℓ P ht hf n tFalse ⤳* hf[(tBox ℓf (tEval ℓ n))..] : P[n..]]; 
  }.

End GenericTyping.

(** This class bundles together the various predicate and relations, and their
properties all together. Most of the logical relation is constructed over an
abstract instance of this class. *)

Class GenericTypingProperties `(ta : tag)
  `(WfContext ta) `(WfType ta) `(Typing ta)
  `(ConvType ta) `(ConvTerm ta) `(ConvNeuConv ta)
  `(RedType ta) `(RedTerm ta)
:=
{
  wfc_prop :: WfContextProperties ;
  wfty_prop :: WfTypeProperties ;
  typ_prop :: TypingProperties ;
  convty_prop :: ConvTypeProperties ;
  convtm_prop :: ConvTermProperties ;
  convne_prop :: ConvNeuProperties ;
  redty_prop :: RedTypeProperties ;
  redtm_prop :: RedTermProperties ;
}.

(** Hints for gen_typing *)
(* Priority 0 *)
#[export] Hint Resolve wfc_wft wfc_ty wfc_convty wfc_convtm wfc_redty wfc_redtm : gen_typing.
(* Priority 2 *)
#[export] Hint Resolve wfc_nil wfc_cons | 2 : gen_typing.
#[export] Hint Resolve wft_wk wft_U wft_prod wft_sig wft_Id | 2 : gen_typing.
#[export] Hint Resolve ty_wk ty_var ty_prod ty_lam ty_app ty_nat ty_bool ty_empty ty_tree ty_zero ty_succ ty_natElim ty_true ty_false ty_alpha ty_boolElim ty_emptyElim ty_leaf ty_node ty_treeElim ty_sig ty_pair ty_fst ty_snd ty_Id ty_refl ty_IdElim| 2 : gen_typing.
#[export] Hint Resolve convty_wk convty_uni convty_prod convty_sig convty_Id | 2 : gen_typing.
#[export] Hint Resolve convtm_wk convtm_prod convtm_sig convtm_eta convtm_nat convtm_bool convtm_empty convtm_tree convtm_zero convtm_succ convtm_true convtm_false convtm_leaf convtm_node convtm_eta_sig convtm_Id convtm_refl | 2 : gen_typing.
#[export] Hint Resolve convneu_wk convneu_var convneu_app convneu_natElim convneu_boolElim convneu_emptyElim convneu_treeElim convneu_fst convneu_snd convneu_IdElim | 2 : gen_typing.
#[export] Hint Resolve redty_ty_src redtm_ty_src | 2 : gen_typing.
(* Priority 4 *)
#[export] Hint Resolve wft_term convty_term convtm_convneu | 4 : gen_typing.
(* Priority 6 *)
#[export] Hint Resolve ty_conv ty_exp convty_exp convtm_exp convtm_conv convneu_conv redtm_conv | 6 : gen_typing.

(** A tactic to transform applications of (untyped) renamings back to (well-typed) weakenings,
so that we can use stability by weakening. *)

Ltac renToWk0 judg :=
  lazymatch judg with
  (** Type judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
(*   (** Type judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on *)

  (** Type conversion judgement, weakening *)
  | [?X ,, ?Y |- ?T⟨↑⟩ ≅ _ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
  | [?X ,, ?Y |- _ ≅ ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply (wk1_ren_on X Y T)
(*   (** Type conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?T⟨upRen_term_term ↑⟩ ≅ _ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (* Type conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- ?T⟨upRen_term_term _⟩ ≅ _ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩  |- _ ≅ ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_wk1_ren_on *)

  (** Term judgement, weakening *)
  | [?X ,, ?Y |- _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
(*   (** Term judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on *)

  (** Term conversion judgement, weakening *)
  | [?X ,, ?Y |- _ ≅ _ : ?T⟨↑⟩ ] =>
    replace T⟨↑⟩ with T⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- ?t⟨↑⟩ ≅ _ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y |- _ ≅ ?t⟨↑⟩ : _ ] =>
    replace t⟨↑⟩ with t⟨@wk1 X Y⟩ by apply wk1_ren_on
(*   (** Term conversion judgement, lifting of weakening *)
  | [?X ,, ?Y ,, ?Z⟨↑⟩ |- _ ≅ _ : _ ] =>
    replace Z⟨↑⟩ with Z⟨@wk1 X Y⟩ by apply wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ _ : ?T⟨upRen_term_term ↑⟩ ] =>
    replace T⟨upRen_term_term ↑⟩ with T⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- ?t⟨upRen_term_term ↑⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  | [?X ,, ?Y ,, ?Z⟨_⟩ |- _ ≅ ?t⟨upRen_term_term ↑⟩ : _ ] =>
    replace t⟨upRen_term_term ↑⟩ with t⟨wk_up Z (@wk1 X Y)⟩ by apply wk_up_wk1_ren_on
  (** Term conversion judgement, lifting *)
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ _ : ?T⟨upRen_term_term _⟩ ] =>
    replace T⟨upRen_term_term r⟩ with T⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- ?t⟨upRen_term_term _⟩ ≅ _ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on
  | [?X ,, ?Y⟨wk_to_ren ?r⟩ |- _ ≅ ?t⟨upRen_term_term _⟩ : _ ] =>
    replace t⟨upRen_term_term r⟩ with t⟨wk_up Y r⟩ by apply wk_up_ren_on *)


  end.

Ltac renToWk :=
  fold ren_term;
  repeat change (ren_term ?x ?y) with y⟨x⟩;
  repeat change S with ↑;
  repeat lazymatch goal with
  | [ _ : _ |- ?G] => renToWk0 G
  end.


(** ** Easy consequences of the previous properties. *)

Section GenericConsequences.
  Context `{ta : tag}
  `{!WfContext ta} `{!WfType ta} `{!Typing ta}
  `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
  `{!RedType ta} `{!RedTerm ta}
  `{!WfContextProperties} `{!WfTypeProperties}
  `{!TypingProperties} `{!ConvTypeProperties}
  `{!ConvTermProperties} `{!ConvNeuProperties}
  `{!RedTypeProperties} `{!RedTermProperties}.



  (** *** Meta-conversion *)
  (** Similar to conversion, but using a meta-level equality rather
  than a conversion *)

  Lemma typing_meta_conv (Γ : context) (t : term) (A A' : decl) :
    [Γ |- t : A] ->
    A' = A ->
    [Γ |- t : A'].
  Proof.
    now intros ? ->.
  Qed.

  Lemma convtm_meta_conv (Γ : context) (t u u' : term) (A A' : decl) :
    [Γ |- t ≅ u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ≅ u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma convne_meta_conv (Γ : context) (t u u' : term) (A A' : decl) :
    [Γ |- t ~ u : A ] ->
    A' = A ->
    u' = u ->
    [Γ |- t ~ u' : A' ].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtm_meta_conv (Γ : context) (t u u' A A' : term) :
    [Γ |- t ⤳* u : A] ->
    A' = A ->
    u' = u ->
    [Γ |- t ⤳* u' : A'].
  Proof.
    now intros ? -> ->.
  Qed.

  Lemma redtmwf_meta_conv_ty (Γ : context) (t u A A' : term) :
    [Γ |- t :⤳*: u : A] ->
    A' = A ->
    [Γ |- t :⤳*: u : A'].
  Proof.
    now intros ? ->.
  Qed.

  (** *** Properties of well-typed reduction *)

  Lemma tyr_wf_l {Γ A B} : [Γ |- A :⤳*: B] -> [Γ |- A].
  Proof.
    intros []; now eapply redty_ty_src.
  Qed.

  Lemma tmr_wf_l {Γ t u A} : [Γ |- t :⤳*: u : A] -> [Γ |- t : A].
  Proof.
    intros []; now eapply redtm_ty_src.
  Qed.

  #[local] Hint Resolve tyr_wf_l tmr_wf_l : gen_typing.
  #[local] Hint Resolve redty_wk redty_term redty_refl redtm_wk redtm_app redtm_refl | 2 : gen_typing.
  #[local] Hint Resolve redtm_beta redtm_natElimZero redtm_natElimSucc redtm_boolElimTrue redtm_boolElimFalse | 2 : gen_typing.
  #[local] Hint Resolve  redtm_conv | 6 : gen_typing.

  Lemma redty_red {Γ A B} :
      [Γ |- A ⤳* B] -> [Γ | A ⤳* B ].
  Proof.
    intros ?%redty_sound.
    assumption.
  Qed.

  Lemma redtm_red {Γ t u A} :
      [Γ |- t ⤳* u : A] ->
      [Γ|t ⤳* u].
  Proof.
    intros ?%redtm_sound.
    assumption.
  Qed.

  #[local] Hint Resolve redty_red  redtm_red | 2 : gen_typing.

  Lemma redtywf_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- A :⤳*: B] -> [Δ |- A⟨ρ⟩ :⤳*: B⟨ρ⟩].
  Proof.
    intros ? []; constructor; gen_typing.
  Qed.

  Lemma redtywf_red {Γ A B} : [Γ |- A :⤳*: B] -> [Γ | A ⤳* B].
  Proof.
    intros []; now eapply redty_red.
  Qed.

  Lemma redtywf_term {Γ A B} :
      [ Γ |- A :⤳*: B : U] -> [Γ |- A :⤳*: B ].
  Proof.
    intros []; constructor; gen_typing.
  Qed.

  Lemma redtywf_refl {Γ A} : [Γ |- A] -> [Γ |- A :⤳*: A].
  Proof.  constructor; gen_typing.  Qed.

  #[global]
  Instance redtywf_trans {Γ} : Transitive (TypeRedWf Γ). (* fun A B => [Γ |- A :⤳*: B] *)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  (** Almost all of the RedTermProperties can be derived
    for the well-formed reduction [Γ |- t :⤳*: u : A]
    but for application (which requires stability of typing under substitution). *)

  Definition redtmwf_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
      [|- Δ ] -> [Γ |- t :⤳*: u : A] -> [Δ |- t⟨ρ⟩ :⤳*: u⟨ρ⟩ : A⟨ρ⟩].
  Proof.  intros ? []; constructor; gen_typing. Qed.

  Definition redtmwf_red {Γ t u A} :
    [Γ |- t :⤳*: u : A] -> [Γ|t ⤳* u].
  Proof. intros []; now eapply redtm_red. Qed.

  Definition redtmwf_conv {Γ} {t u A B} :
      [Γ |- t :⤳*: u : A] ->
      [Γ |- A ≅ B ] ->
      [Γ |- t :⤳*: u : B].
  Proof.
    intros [wfl red] ?.
    constructor.
    all: gen_typing.
  Qed.

  Lemma redtmwf_refl {Γ} {a A : term} : [Γ |- a : A] -> [Γ |- a :⤳*: a : A].
  Proof.
    constructor; tea.
    now apply redtm_refl.
  Qed.

  #[global]
  Instance redtmwf_trans {Γ A} : Transitive (TermRedWf Γ A). (*fun t u => [Γ |- t :⤳*: u : A]*)
  Proof.
    intros ??? [] []; unshelve econstructor; try etransitivity; tea.
  Qed.

  Definition convty_wfexp {Γ A A' B B'} :
    [Γ |- A :⤳*: A'] ->
    [Γ |- B :⤳*: B'] ->
    [Γ |- A' ≅ B'] ->
    [Γ |- A ≅ B].
  Proof.
    intros; eapply convty_exp; gtyping.
  Qed.

  Definition convtm_wfexp {Γ A A' t t' u u'} :
    [Γ |- A :⤳*: A'] ->
    [Γ |- t :⤳*: t' : A'] ->
    [Γ |- u :⤳*: u' : A'] ->
    [Γ |- t' ≅ u' : A'] ->
    [Γ |- A' ≅ A'] ->
    [Γ |- t ≅ u : A].
  Proof.
    intros.
    assert [Γ |- A' ≅ A] by (eapply convty_wfexp; tea; gtyping).
    eapply convtm_conv; tea.
    eapply convtm_exp; tea; gtyping.
  Qed.


  Lemma redtmwf_app {Γ A B f f' t} :
    [ Γ |- f :⤳*: f' : tProd A B ] ->
    [ Γ |- t : A ] ->
    [ Γ |- tApp f t :⤳*: tApp f' t : B[t..] ].
  Proof.
    intros [] ?; constructor; gen_typing.
  Qed.

  Lemma redtmwf_appwk {Γ Δ A B B' t u a} (ρ : Δ ≤ Γ) :
    [Γ |- t :⤳*: u : tProd A B] ->
    [Δ |- a : term_decl A⟨ρ⟩] ->
    B' = B⟨wk_up A ρ⟩[a..] ->
    [Δ |- tApp t⟨ρ⟩ a :⤳*: tApp u⟨ρ⟩ a : B'].
  Proof.
    intros redtu **.
    eapply redtmwf_meta_conv_ty; tea.
    eapply redtmwf_app; tea.
    unshelve eapply (redtmwf_wk ρ _ redtu).
    gen_typing.
  Qed.

  Lemma redtmwf_natElimZero {Γ P hz hs} :
    [Γ ,, tNat |- P ] ->
    [Γ |- hz : term_decl P[tZero..]] ->
    [Γ |- hs : elimSuccHypTy' Γ P] ->
    [Γ |- tNatElim P hz hs tZero :⤳*: hz : P[tZero..]].
  Proof.
    intros ???; constructor; tea; gen_typing.
  Qed.

  Lemma redtmwf_boolElimTrue {Γ P ht hf} :
    [Γ ,, tBool |- P ] ->
    [Γ |- ht : term_decl P[tTrue..]] ->
    [Γ |- hf : term_decl P[tFalse..]] ->
    [Γ |- tBoolElim P ht hf tTrue :⤳*: ht : P[tTrue..]].
  Proof.
    intros ???; constructor; tea; gen_typing.
  Qed.

  Lemma redtmwf_boolElimFalse {Γ P ht hf} :
    [Γ ,, tBool |- P ] ->
    [Γ |- ht : term_decl P[tTrue..]] ->
    [Γ |- hf : term_decl P[tFalse..]] ->
    [Γ |- tBoolElim P ht hf tFalse :⤳*: hf : P[tFalse..]].
  Proof.
    intros ???; constructor; tea; gen_typing.
  Qed.

  (** *** Properties of well-typing *)

  Definition well_typed_well_formed Γ t : well_typed Γ t -> well_formed Γ t :=
  fun w =>
  {|
    well_formed_class := isterm (well_typed_type Γ t w) ;
    well_formed_typed := well_typed_typed Γ t w
  |}.

  #[warning="-uniform-inheritance"]Coercion well_typed_well_formed : well_typed >-> well_formed.

  Definition well_formed_well_typed Γ t (w : well_formed Γ t) : (well_typed Γ t + [Γ |- t]) :=
  (match (well_formed_class _ _ w) as c return
      (match c with
      | istype => [Γ |-[ ta ] t]
      | isterm A => [Γ |-[ ta ] t : A]
      end -> well_typed Γ t + [Γ |-[ ta ] t])
  with
  | istype => inr
  | isterm A => fun w' => inl {| well_typed_type := A ; well_typed_typed := w' |}
    end) (well_formed_typed _ _ w).

  (** *** Derived typing, reduction and conversion judgements *)


  Lemma wfc_consε {Γ F} : [|-Γ] -> [|-Γ,,↦ F].
  Proof.
    intros wfΓ. destruct F as [F wfF].
    induction F as [ | [n b] F IHF].
    + now eapply wfc_alpha.
    + rename wfF into wfFn.
      set (ltn := wfFn.(Spr1)).
      set (wfF := wfFn.(Spr2) : ell_wf F).
      specialize (IHF wfF).
      replace (Γ,, ↦ _) with (Γ,, ↦ Build_ell F wfF,, index_0 : (wfFcons_new wfFn) ↦ b).
      { eapply wfc_consF; tea. }
      cbn. unfold cons_ell. f_equal. f_equal.
      eapply ell_eq.
      destruct F as [ | [n' b'] F].
      - cbn. reflexivity.
      - cbn.
        destruct (Compare_dec.lt_dec n n').
        * reflexivity.
        * assert SFalse as [].
          destruct ltn as [[ltn]].
          destruct (n0 ltn).
  Qed.

  Lemma wk1_ren_on_decl Γ (t A : decl) :t⟨@wk1 Γ A⟩ = t⟨↑⟩.
  Proof.
    destruct t.
    - eapply (f_equal term_decl), wk1_ren_on.
    - reflexivity.
  Qed.

  Lemma ty_var0' {Γ A} :
    [|- Γ,, A] ->
    [Γ ,, A |- tRel 0 : A⟨@wk1 Γ A⟩].
  Proof.
    intros.
    rewrite wk1_ren_on_decl.
    intros; refine (ty_var H7 (in_here _ _ : in_ctx (Γ,,A) _ _)).
  Qed.
  Lemma ty_var0 {Γ A} :
    [Γ |- A] ->
    [Γ ,, A |- tRel 0 : term_decl A⟨@wk1 Γ A⟩].
  Proof.
    intros.
    refine (ty_var0' _); gtyping.
  Qed.

  Lemma wft_simple_arr {Γ A B} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- arr' Γ A B].
  Proof.
    intros. eapply wft_prod; renToWk; tea.
    eapply wft_wk; gen_typing.
  Qed.

  Lemma convty_simple_arr {Γ A A' B B'} :
    [Γ |- A] ->
    [Γ |- A ≅ A'] ->
    [Γ |- B ≅ B'] ->
    [Γ |- arr' Γ A B ≅ arr' Γ A' B'].
  Proof.
    intros; eapply convty_prod; tea.
    rewrite (wk1_ren_on Γ A'), <- (wk1_ren_on Γ A).
    eapply convty_wk; gen_typing.
  Qed.

  Lemma ty_simple_app {Γ A B f a} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- f : arr' Γ A B] ->
    [Γ |- a : A] ->
    [Γ |- tApp f a : B].
  Proof.
    intros. rewrite <- (@shift_subst1 Γ A B a).
    eapply ty_app; tea.
  Qed.

  Lemma convneu_simple_app {Γ} {f g t u A B : term} :
      [ Γ |- f ~ g : arr' Γ A B ] ->
      [ Γ |- t ≅ u : A ] ->
      [ Γ |- tApp f t ~ tApp g u : B ].
  Proof.
    intros. rewrite <- (@shift_subst1 Γ A B t).
    now eapply convneu_app.
  Qed.

  #[local]
  Hint Resolve ty_simple_app : gen_typing.

  Lemma ty_id {Γ A B C} :
    [Γ |- A] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ |- idterm A : arr' Γ B C].
  Proof.
    intros.
    eapply ty_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply ty_lam; tea.
    renToWk.
    now eapply ty_var0.
  Qed.

  Lemma ty_id' {Γ A} :
    [Γ |- A] ->
    [Γ |- idterm A : arr' Γ A A].
  Proof.
    intros.
    (* eapply ty_conv. *)
    (* 2: eapply convty_simple_arr; cycle 1; tea. *)
    eapply ty_lam; tea.
    renToWk.
    now eapply ty_var0.
  Qed.

  Lemma redtm_id_beta {Γ a A} :
    [Γ |- A] ->
    [Γ |- A ≅ A] ->
    [Γ |- a : A] ->
    [Γ |- tApp (idterm A) a ⤳* a : A].
  Proof.
    intros.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + now eapply ty_var0.
    + cbn; now bsimpl.
    + now asimpl.
  Qed.

  Lemma convtm_id {Γ A A' B C} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ |- A ≅ A'] ->
    [Γ |- A ≅ B] ->
    [Γ |- A ≅ C] ->
    [Γ,, A |- tRel 0 ≅ tRel 0 : term_decl A⟨@wk1 Γ A⟩] ->
    [Γ |- idterm A ≅ idterm A' : arr' Γ B C].
  Proof.
    intros.
    assert [Γ |- A ≅ A] by (etransitivity; tea; now symmetry).
    eapply convtm_conv.
    2: eapply convty_simple_arr; cycle 1; tea.
    eapply convtm_eta; tea.
    { apply wft_wk; [apply wfc_cons|]; tea. }
    2:{ constructor; first [now eapply lrefl|now apply ty_var0|tea]. }
    3:{ constructor; first [now eapply lrefl|now apply ty_var0|tea]. }
    1,2: eapply ty_id; tea; now symmetry.
    assert [|- Γ,, A] by gen_typing.
    assert [Γ,, A |-[ ta ] A⟨@wk1 Γ A⟩] by now eapply wft_wk.
    eapply convtm_exp.
    - rewrite <- wk_lam.
      eapply redtm_id_beta.
      3: now eapply ty_var0.
      1,2: tea; now eapply convty_wk.
    - rewrite <- wk_lam.
      assert [Γ,, A |- A'⟨@wk1 Γ A⟩ ≅ A⟨@wk1 Γ A⟩]
        by (symmetry; now eapply convty_wk).
      eapply redtm_conv; tea.
      eapply redtm_id_beta.
      1: renToWk; now eapply wft_wk.
      1: now eapply lrefl.
      eapply ty_conv. 2: now symmetry.
      now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - now eapply ty_var0.
    - now eapply ty_var0.
    - renToWk; tea; now eapply convty_wk.
    - eassumption.
  Qed.

  Lemma ty_comp {Γ A B C f g} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- g : arr' Γ A B] ->
    [Γ |- f : arr' Γ B C] ->
    [Γ |- comp' Γ A f g : arr' Γ A C].
  Proof.
    intros tyA tyB **.
    eapply ty_lam ; tea.
    assert [|- Γ,, A] by gen_typing.
    eapply ty_simple_app.
    - unshelve eapply (wft_wk (@wk1 Γ A) _ tyB) ; tea.
    - now eapply wft_wk.
    - rewrite wk_arr', wk_decl.
      now eapply ty_wk.
    - eapply ty_simple_app.
      + unshelve eapply (wft_wk (@wk1 Γ A) _ tyA) ; tea.
      + now eapply wft_wk.
      + rewrite wk_arr', wk_decl.
        now eapply ty_wk.
      + now eapply ty_var0.
  Qed.

  Lemma wft_wk1 {Γ A B} : [Γ |- A] -> [Γ |- B] -> [Γ ,, A |- B⟨@wk1 Γ A⟩].
  Proof. intros; eapply wft_wk; gen_typing. Qed.
  Lemma ty_wk1 {Γ A B t} : [Γ |- A] -> [Γ |- t : B] -> [Γ ,, A |- t⟨@wk1 Γ A⟩ : B⟨@wk1 Γ A⟩].
  Proof. intros; eapply ty_wk; gen_typing. Qed.

  Lemma redtm_comp_beta {Γ A B C f g a} :
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- f : arr' Γ A B] ->
    [Γ |- g : arr' Γ B C] ->
    [Γ |- a : A] ->
    [Γ |- tApp (comp' Γ A g f) a ⤳* tApp g (tApp f a) : C].
  Proof.
    intros hA hB hC hf hg ha.
    eapply redtm_meta_conv.
    1: eapply redtm_beta; tea.
    + eapply ty_simple_app.
      4: eapply ty_simple_app.
      1,2,4,5: eapply wft_wk1; [gen_typing|].
      1: exact hB. 1: exact hC. 1: exact hA. 1: tea.
      1,2: rewrite wk_arr', wk_decl; eapply ty_wk ; tea; gen_typing.
      now eapply ty_var0.
    + now rewrite shift_subst1.
    + cbn. now rewrite 2shift_subst1.
  Qed.

  Lemma convtm_comp_app {Γ A B C f f' g g'} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- C ≅ C] ->
    [Γ |- f : arr' Γ A B] ->
    [Γ |- f' : arr' Γ A B] ->
    [Γ |- g : arr' Γ B C] ->
    [Γ |- g' : arr' Γ B C] ->
    [Γ,, A |- tApp g⟨@wk1 Γ A⟩ (tApp f⟨@wk1 Γ A⟩ (tRel 0)) ≅ tApp g'⟨@wk1 Γ A⟩ (tApp f'⟨@wk1 Γ A⟩ (tRel 0)) : term_decl C⟨@wk1 Γ A⟩] ->
    [Γ ,, A |- tApp (comp' Γ A g f)⟨@wk1 Γ A⟩ (tRel 0) ≅ tApp (comp' Γ A g' f')⟨@wk1 Γ A⟩ (tRel 0) : term_decl C⟨@wk1 Γ A⟩].
  Proof.
    intros.
    eapply convtm_exp.
    - rewrite wk_comp'.
      eapply redtm_comp_beta.
      5: erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      4: erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - rewrite wk_comp'.
      eapply redtm_comp_beta.
      5: erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      4: erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      1-3: now eapply wft_wk1.
      now eapply ty_var0.
    - now eapply wft_wk1.
    - eapply @ty_simple_app with (A := B⟨@wk1 Γ A⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨@wk1 Γ A⟩);
          [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
    - eapply @ty_simple_app with (A := B⟨@wk1 Γ A⟩).
      + now eapply wft_wk1.
      + now eapply wft_wk1.
      + erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
      + eapply @ty_simple_app with (A := A⟨@wk1 Γ A⟩);
          [now eapply wft_wk1|now eapply wft_wk1| |now apply ty_var0].
        erewrite wk_arr', wk_decl; eapply ty_wk; tea; gen_typing.
    - apply convty_wk; gen_typing.
    - assumption.
  Qed.


  Lemma convtm_comp {Γ A B C f f' g g'} :
    [|- Γ] ->
    [Γ |- A] ->
    [Γ |- A ≅ A] ->
    [Γ |- B] ->
    [Γ |- C] ->
    [Γ |- C ≅ C] ->
    [Γ |- f : arr' Γ A B] ->
    [Γ |- f' : arr' Γ A B] ->
    [Γ |- g : arr' Γ B C] ->
    [Γ |- g' : arr' Γ B C] ->
    [Γ,, A |-[ ta ] tApp g⟨@wk1 Γ A⟩ (tApp f⟨@wk1 Γ A⟩ (tRel 0)) ≅
      tApp g'⟨@wk1 Γ A⟩ (tApp f'⟨@wk1 Γ A⟩ (tRel 0)) : term_decl C⟨@wk1 Γ A⟩] ->
    [Γ |- comp' Γ A g f ≅ comp' Γ A g' f' : arr' Γ A C].
  Proof.
(*     change ((ren1 (Y:=term) (Z:=decl) ?ρ C)) with (term_decl C⟨ρ⟩). *)
    intros.
    eapply convtm_eta; tea.
    1: now eapply wft_wk1.
    2:{ constructor; tea.
        eapply ty_simple_app, ty_simple_app, ty_var0 ; tea.
        3,6 : erewrite wk_arr', wk_decl.
        3,4: now eapply ty_wk1.
        all: now apply wft_wk1. }
    3:{ constructor; tea.
        eapply ty_simple_app, ty_simple_app, ty_var0; tea.
        3,6 : erewrite wk_arr', wk_decl.
        3,4: now eapply ty_wk1.
        all: now apply wft_wk1. }
    1,2: eapply ty_comp.
    4,5,9,10: tea.
    all: tea.
    eapply convtm_comp_app; cycle 4; tea.
  Qed.

  Lemma typing_eta (Γ : context) A B f :
    [Γ |- A] ->
    [Γ,, A |- B] ->
    [Γ |- f : tProd A B] ->
    [Γ,, A |- eta_expand' Γ A f : B].
  Proof.
    intros ? ? Hf.
    eapply typing_meta_conv.
    eapply ty_app; tea.
    2: now eapply ty_var0.
    1: erewrite wk_prod, wk_decl; eapply ty_wk1; tea.
    now rewrite wk1_eta.
  Qed.

  Lemma lambda_cong {Γ} {A A' B B' t t' : term} :
    [Γ |- A] ->
    [Γ |- A'] ->
    [Γ,, A |- B] ->
    [Γ,, A |- t : B] ->
    [Γ,, A |- t' : B] ->
    [Γ,, A' |- t' : B'] ->
    [Γ |- A ≅ A'] ->
    [Γ,, A |- B ≅ B'] ->
    [Γ,, A' |- B ≅ B'] ->
    [Γ,, A |- t ≅ t' : B] ->
    [Γ |- tLambda A t ≅ tLambda A' t' : tProd A B].
  Proof.
    intros.
    assert [|- Γ,, A] by gen_typing.
    apply convtm_eta ; tea.
    - gen_typing.
    - constructor; first[now eapply lrefl|tea].
    - eapply ty_conv.
      1: eapply ty_lam ; tea.
      symmetry.
      now eapply convty_prod.
    - constructor; tea.
    - rewrite <-2 wk_lam.
      eapply @convtm_exp with (t' := t) (u' := t'); tea.
      3: now eapply lrefl.
      2: eapply redtm_conv ; cbn ; [eapply redtm_meta_conv |..] ; [eapply redtm_beta |..].
      1: eapply redtm_meta_conv ; cbn ; [eapply redtm_beta |..].
      + now eapply wft_wk.
      + rewrite wk_decl.
        eapply ty_wk with (2:=H10).
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_var0 ; tea.
      + symmetry; exact wk1_eta.
      + symmetry; exact wk1_eta.
      + now eapply wft_wk.
      + rewrite wk_decl.
        eapply ty_wk with (2:=H12).
        eapply wfc_cons ; tea.
        now eapply wft_wk.
      + eapply ty_conv.
        1: eapply ty_var0 ; tea.
        now eapply convty_wk.
      + symmetry; exact wk1_eta.
      + symmetry; exact wk1_eta.
      + symmetry. eassumption.
  Qed.

  Lemma ty_app_ren {Γ Δ} {A f a dom cod : term} (ρ : Δ ≤ Γ) :
    [Γ |- f : A] -> [Γ |- A ≅ tProd dom cod] ->
    [Δ |- a : term_decl dom⟨ρ⟩] -> [Δ |- tApp f⟨ρ⟩ a : term_decl cod⟨wk_up dom ρ⟩[a ..]].
  Proof.
    intros Hf HA Ha.
    eapply ty_app, Ha.
    rewrite wk_prod, wk_decl; gtyping.
  Qed.

  Lemma convneu_app_ren {Γ Δ} {A f g a b dom cod : term} (ρ : Δ ≤ Γ) :
    [Γ |- f ~ g : A ] ->
    [Γ |- A ≅ tProd dom cod] ->
    [Δ |- a ≅ b : term_decl dom⟨ρ⟩] ->
    [Δ |- tApp f⟨ρ⟩ a ~ tApp g⟨ρ⟩ b : term_decl cod⟨wk_up dom ρ⟩[a ..]].
  Proof.
    intros Hfg HA Hab.
    eapply convneu_app, Hab.
    rewrite wk_prod, wk_decl ; gtyping.
  Qed.



  (** *** Lifting determinism properties from untyped reduction to typed reduction. *)

  Lemma redtm_whnf {Γ t u A} : [Γ |- t ⤳* u : A] -> whnf t -> t = u.
  Proof.
    intros.
    eapply red_whnf; [|assumption].
    now eapply redtm_sound.
  Qed.

  Lemma redtmwf_whnf {Γ t u A} : [Γ |- t :⤳*: u : A] -> whnf t -> t = u.
  Proof.
    intros []; now eapply redtm_whnf.
  Qed.

  Lemma redtmwf_whne {Γ t u A} : [Γ |- t :⤳*: u : A] -> whne t -> t = u.
  Proof.
    intros ? ?%whnf_whne; now eapply redtmwf_whnf.
  Qed.

  Lemma redty_whnf {Γ A B} : [Γ |- A ⤳* B] -> whnf A -> A = B.
  Proof.
    intros.
    eapply red_whnf; [|eassumption].
    now eapply redty_sound.
  Qed.

  Lemma redtywf_whnf {Γ A B} : [Γ |- A :⤳*: B] -> whnf A -> A = B.
  Proof.
    intros []; now eapply redty_whnf.
  Qed.

  Lemma redtywf_whne {Γ A B} : [Γ |- A :⤳*: B] -> whne A -> A = B.
  Proof.
    intros ? ?%whnf_whne; now eapply redtywf_whnf.
  Qed.

  Lemma redtmwf_det {Γ t u u' A A'} :
    whnf u -> whnf u' ->
    [Γ |- t :⤳*: u : A] -> [Γ |- t :⤳*: u' : A'] ->
    u = u'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  Lemma redtywf_det {Γ A B B'} :
    whnf B -> whnf B' ->
    [Γ |- A :⤳*: B] -> [Γ |- A :⤳*: B'] ->
    B = B'.
  Proof.
    intros ?? [] [].
    eapply whred_det; tea.
    all: now eapply redty_sound.
  Qed.

  Lemma whredtm_det {Γ t A A'} (red1 : [Γ |- t ↘ A]) (red2 : [Γ |- t ↘ A']) :
    red1.(tmred_whnf) = red2.(tmred_whnf).
  Proof.
    destruct red1 as [? []], red2 as [? []]; cbn.
    eapply whred_det; tea.
    all: now eapply redtm_sound.
  Qed.

  Lemma whredty_det {Γ A} (red1 : [Γ |- A ↘]) (red2 : [Γ |- A ↘]) :
   red1.(tyred_whnf) = red2.(tyred_whnf).
  Proof.
    destruct red1 as [? []], red2 as [? []]; cbn.
    eapply whred_det; try eapply isType_whnf; tea.
    all: now eapply redty_sound.
  Qed.

  Lemma whredtm_ty_det {Γ t A} (whrty : [Γ |- t ↘ ]) (whrtm : [Γ |- t ↘  A]) : whrty.(tyred_whnf) = whrtm.(tmred_whnf).
  Proof. eapply whred_det; gtyping. Qed.

  Lemma whredty_whnf {Γ A} (whA : [Γ |- A ↘ ]) : whnf A -> A = whA.(tyred_whnf).
  Proof.
    destruct whA; cbn; now eapply redtywf_whnf.
  Qed.

  Lemma whredtm_whnf {Γ A t} (wht : [Γ |- t ↘ A ]) : whnf t -> t = wht.(tmred_whnf).
  Proof.
    destruct wht; cbn; now eapply redtmwf_whnf.
  Qed.

  Lemma isWfFun_isFun : forall Γ A B t, isWfFun Γ A B t -> isFun t.
  Proof.
  intros * []; econstructor. now eapply convneu_whne.
  Qed.

  Lemma isWfPair_isPair : forall Γ A B t, isWfPair Γ A B t -> isPair t.
  Proof.
  intros * []; econstructor; now eapply convneu_whne.
  Qed.


  Lemma ty_nSucc {Γ n t} :
    [Γ |- t : tNat] ->
    [Γ |- nSucc n t : tNat].
  Proof.
    intros ht; induction n.
    - tea.
    - cbn. now eapply ty_succ.
  Qed.

  Lemma convtm_nSucc {Γ n t t'} :
    [Γ |- t ≅ t': tNat] ->
    [Γ |- nSucc n t ≅ nSucc n t': tNat].
  Proof.
    intros ht; induction n.
    - tea.
    - cbn. now eapply convtm_succ.
  Qed.

End GenericConsequences.


#[export] Hint Resolve tyr_wf_l tmr_wf_l well_typed_well_formed : gen_typing.
#[export] Hint Resolve redtywf_wk redtywf_term redtywf_red redtywf_refl redtmwf_wk redtmwf_app redtmwf_refl redtm_beta redtmwf_red redtmwf_natElimZero redtmwf_boolElimTrue redtmwf_boolElimFalse| 2 : gen_typing.
#[export] Hint Resolve  redtmwf_conv | 6 : gen_typing.

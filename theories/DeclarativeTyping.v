(** * LogRel.DeclarativeTyping: specification of conversion and typing, in a declarative fashion. *)
From Stdlib Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel Require Import Utils Syntax.All.

Set Primitive Projections.

(** Definitions in this file should be understood as the _specification_ of conversion
or typing, done in a declarative fashion. For instance, we _demand_ that conversion
be transitive by adding a corresponding rule. *)

(** ** Definitions *)
Section Definitions.

  (* We locally disable typing notations to be able to use them in the definition
  here before declaring the instance to which abstract notations are bound. *)
  Close Scope typing_scope.


  (** Typing and conversion are mutually defined inductive relations. To avoid having
  to bother with elimination of propositions, we put them in the Type sort. *)
(* Reserved Notation "[ Γ |- m ~ n : A ]" (at level 0, m, n, A at level 50).
Reserved Notation "[ Γ |- m ≅ n : A ]" (at level 0, m, n, A at level 50).
Reserved Notation "[ Γ |- m ≅ n ]" (at level 0, m, n at level 50).
Reserved Notation "[ Γ |- m ]" (at level 0, m at level 50).
Reserved Notation "[ Γ |- m : A ]" (at level 0, m, A at level 50).
Reserved Notation "[ |- Γ ]" (at level 0). *)
  (** **** Context well-formation *)
  Inductive WfContextDecl : context -> Type :=
      | connil : [ |- ε ]
      | connew {Γ i new b} : [|-Γ] -> [|-Γ ,, i : new ↦ b]
      | conalpha {Γ} : [|-Γ] -> [|- Γ ,, ↦ nil_ell]
      | concons {Γ A} :
          [ |- Γ ] ->
          [ Γ |- A ] ->
          [ |-  Γ ,, A]
      | conell {Γ} {ℓ : ell} :
          [ |- Γ ] ->
          [ |- Γ ,, ℓ]
  (** **** Type well-formation *)
  with WfTypeDecl : context -> term -> Type :=
      | wfTypeU {Γ} :
          [ |- Γ ] ->
          [ Γ |- U ]
      | wfTypeProd {Γ} {A B} :
          [ Γ |- A ] ->
          [Γ ,, A |- B ] ->
          [ Γ |- tProd A B ]
      | wfTypeNat {Γ} :
          [|- Γ] ->
          [Γ |- tNat]
      | wfTypeBool {Γ} :
          [|- Γ] ->
          [Γ |- tBool]
      | wfTypeEmpty {Γ} :
          [|- Γ] ->
          [Γ |- tEmpty]
      | wfTypeTree {Γ} :
          [|- Γ] ->
          [Γ |- tTree]
      | wfTypeSig {Γ} {A B} :
          [ Γ |- A ] ->
          [Γ ,, A |- B ] ->
          [ Γ |- tSig A B ]
      | wftTypeId {Γ} {A x y} :
          [Γ |- A] ->
          [Γ |- x : A] ->
          [Γ |- y : A] ->
          [Γ |- tId A x y]
      | wfTypeUniv {Γ} {A} :
          [ Γ |- A : U ] ->
          [ Γ |- A ]
      | wfTypeSplit {Γ A i new} :
          [|- Γ] ->
          [ Γ,, i : new ↦ true |- A] ->
          [ Γ,, i : new ↦ false |- A] ->
          [ Γ |- A]
  (** **** Typing *)
  with TypingDecl : context -> decl -> term -> Type :=
      | wfVar {Γ} {n d} :
          [   |- Γ ] ->
          in_ctx Γ n d ->
          [ Γ |- tRel n : d ]
      | wfTermProd {Γ} {A B} :
          [ Γ |- A : U] -> 
          [Γ ,, A |- B : U ] ->
          [ Γ |- tProd A B : U ]
      | wfTermLam {Γ} {A B t : term} :
          [ Γ |- A ] ->
          [ Γ ,, A |- t : B ] -> 
          [ Γ |- tLambda A t : tProd A B]
      | wfTermApp {Γ} {f a A B} :
          [ Γ |- f : tProd A B ] -> 
          [ Γ |- a : A ] -> 
          [ Γ |- tApp f a : term_decl B[a..] ]
      | wfTermNat {Γ} :
          [|-Γ] ->
          [Γ |- tNat : U]
      | wfTermZero {Γ} :
          [|-Γ] ->
          [Γ |- tZero : tNat]
      | wfTermSucc {Γ n} :
          [Γ |- n : tNat] ->
          [Γ |- tSucc n : tNat]
      | wfTermNatElim {Γ P hz hs n} :
        [Γ ,, tNat |- P ] ->
        [Γ |- hz : term_decl P[tZero..]] ->
        [Γ |- hs : elimSuccHypTy' Γ P] ->
        [Γ |- n : tNat] ->
        [Γ |- tNatElim P hz hs n : term_decl P[n..]]
      | wfTermBool {Γ} :
          [|-Γ] ->
          [Γ |- tBool : U]
      | wfTermTrue {Γ} :
          [|-Γ] ->
          [Γ |- tTrue : tBool]
      | wfTermFalse {Γ} :
          [|-Γ] ->
          [Γ |- tFalse : tBool]
      | wfTermBoolElim {Γ P ht hf n} :
        [Γ ,, tBool |- P ] ->
        [Γ |- ht : term_decl P[tTrue..]] ->
        [Γ |- hf : term_decl  P[tFalse..]] ->
        [Γ |- n : tBool] ->
        [Γ |- tBoolElim P ht hf n : term_decl P[n..]]
      | wfTermAlpha {Γ : context} {i : list_index Γ} :
          [|- Γ] ->
          [ Γ |- tAlpha i : arr' Γ tNat tBool]
      | wfTermEmpty {Γ} :
          [|-Γ] ->
          [Γ |- tEmpty : U]
      | wfTermEmptyElim {Γ P e} :
        [Γ ,, tEmpty |- P ] ->
        [Γ |- e : tEmpty] ->
        [Γ |- tEmptyElim P e : term_decl P[e..]]
      | wfTermTree {Γ} :
          [|-Γ] ->
          [Γ |- tTree : U]
      | wfTermLeaf {Γ n} :
          [Γ |- n : tNat] ->
          [Γ |- tLeaf n : tTree]
      | wfTermNode {Γ n tl tr} :
          [Γ |- n : tNat] ->
          [Γ |- tl : tTree] ->
          [Γ |- tr : tTree] ->
          [Γ |- tNode n tl tr : tTree]
      | wfTermTreeElim {Γ P hl hn t} :
        [Γ ,, tTree |- P ] ->
        [Γ |- hl : elimLeafHypTy' Γ P] ->
        [Γ |- hn : elimNodeHypTy' Γ P] ->
        [Γ |- t : tTree] ->
        [Γ |- tTreeElim P hl hn t : term_decl P[t..]]
      | wfTermSig {Γ} {A B} :
        [ Γ |- A : U] -> 
        [Γ ,, A |- B : U ] ->
        [ Γ |- tSig A B : U ]
      | wfTermPair {Γ} {A B a b} :
        [Γ |- A] ->
        [Γ,, A |- B] ->
        [Γ |- a : A] -> 
        [Γ |- b : term_decl B[a..]] ->
        [Γ |- tPair A B a b : tSig A B]
      | wfTermFst {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tFst p : A]
      | wfTermSnd {Γ A B p} :
        [Γ |- p : tSig A B] ->
        [Γ |- tSnd p : term_decl B[(tFst p)..]]
      | wfTermId {Γ} {A x y} :
          [Γ |- A : U] ->
          [Γ |- x : A] ->
          [Γ |- y : A] ->
          [Γ |- tId A x y : U]
      | wfTermRefl {Γ A x} :
          [Γ |- A] ->
          [Γ |- x : A] ->
          [Γ |- tRefl A x : tId A x x]
      | wfTermIdElim {Γ A x P hr y e} :
          [Γ |- A] ->
          [Γ |- x : A] ->
          [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P] ->
          [Γ |- hr : term_decl P[tRefl A x .: x..]] ->
          [Γ |- y : A] ->
          [Γ |- e : tId A x y] ->
          [Γ |- tIdElim A x P hr y e : term_decl P[e .: y..]]
      | wfTermConv {Γ} {t A B : term} :
          [ Γ |- t : A ] -> 
          [ Γ |- A ≅ B ] -> 
          [ Γ |- t : B ]
      | wfTermSplit {Γ t A i new} :
          [ |-  Γ] ->
          [ Γ,, i : new ↦ true |- t : A] ->
          [ Γ,, i : new ↦ false |- t : A] ->
          [ Γ |- t : A]
      | wfTermXi {Γ t} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t : tNat] ->
          [ Γ |- tXi ℓ t : tTree]
      | wfTermXXi {Γ t u} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t : tNat] -> [ Γ |- u : ℓ] ->
          [ Γ |- tXXi ℓ t u : tId tNat (dEval' Γ (tXi ℓ t) (tEval ℓ u)) t[u..] ]
      | wfTermEval {Γ t} {ℓ : ell} :
          [ Γ |- t : ℓ ] ->
          [ Γ |- tEval ℓ t : arr' Γ tNat tBool]
      | wfTermBox {Γ t} {ℓ : ell} :
          [ Γ |- t : arr' Γ tNat tBool] ->
          (forall n b, in_ell ℓ n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
          [ Γ |- tBox ℓ t : ℓ]
      | wfTermEllElim {Γ ℓ k P ht hf n b} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          [ Γ,, ℓ |- P] ->
          [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
          [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
          [ Γ |- n : ℓ] -> [Γ |- b : tBool] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
          [ Γ |- tEllElim k ℓ P ht hf n b : term_decl P[n..] ]
  (** **** Conversion of types *)
  with ConvTypeDecl : context -> term -> term  -> Type :=  
      | TypePiCong {Γ} {A B C D} :
          [ Γ |- A] ->
          [ Γ |- A ≅ B] ->
          [ Γ ,, A |- C ≅ D] ->
          [ Γ |- tProd A C ≅ tProd B D]
      | TypeSigCong {Γ} {A B C D} :
          [ Γ |- A] ->
          [ Γ |- A ≅ B] ->
          [ Γ ,, A |- C ≅ D] ->
          [ Γ |- tSig A C ≅ tSig B D]
      | TypeIdCong {Γ A A' x x' y y'} :
          (* [Γ |- A] -> ?  *)
          [Γ |- A ≅ A'] ->
          [Γ |- x ≅ x' : A] ->
          [Γ |- y ≅ y' : A] ->
          [Γ |- tId A x y ≅ tId A' x' y' ]
      | TypeRefl {Γ} {A} : 
          [ Γ |- A ] ->
          [ Γ |- A ≅ A]
      | convUniv {Γ} {A B} :
        [ Γ |- A ≅ B : U ] -> 
        [ Γ |- A ≅ B ]
      | TypeSym {Γ} {A B} :
          [ Γ |- A ≅ B ] ->
          [ Γ |- B ≅ A ]
      | TypeTrans {Γ} {A B C} :
          [ Γ |- A ≅ B] ->
          [ Γ |- B ≅ C] ->
          [ Γ |- A ≅ C]
      | TypeSplit {Γ A B i new} :
          [|- Γ] ->
          [ Γ,, i : new ↦ true |- A ≅ B] ->
          [ Γ,, i : new ↦ false |- A ≅ B] ->
          [ Γ |- A ≅ B]
  (** **** Conversion of terms *)
  with ConvTermDecl : context -> decl -> term -> term -> Type :=
      | TermBRed {Γ} {a t A B : term} :
              [ Γ |- A ] ->
              [ Γ ,, A |- t : B ] ->
              [ Γ |- a : A ] ->
              [ Γ |- tApp (tLambda A t) a ≅ t[a..] : term_decl B[a..] ]
      | TermPiCong {Γ} {A B C D} :
          [ Γ |- A : U] ->
          [ Γ |- A ≅ B : U ] ->
          [ Γ ,, A |- C ≅ D : U ] ->
          [ Γ |- tProd A C ≅ tProd B D : U ]
      | TermAppCong {Γ} {a b f g A B} :
          [ Γ |- f ≅ g : tProd A B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- tApp f a ≅ tApp g b : term_decl B[a..] ]
      | TermLambdaCong {Γ} {t u A A' A'' B : term} :
          [ Γ |- A ] ->
          [ Γ |- A ≅ A' ] ->
          [ Γ |- A ≅ A'' ] ->
          [ Γ,, A |- t ≅ u : B ] ->
          [ Γ |- tLambda A' t ≅ tLambda A'' u : tProd A B ]
      | TermFunEta {Γ} {f A B} :
          [ Γ |- f : tProd A B ] ->
          [ Γ |- tLambda A (eta_expand' Γ A f) ≅ f : tProd A B ]
      | TermSuccCong {Γ} {n n'} :
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tSucc n ≅ tSucc n' : tNat]
      | TermNatElimCong {Γ P P' hz hz' hs hs' n n'} :
          [Γ ,, tNat |- P ≅ P'] ->
          [Γ |- hz ≅ hz' : term_decl P[tZero..]] ->
          [Γ |- hs ≅ hs' : elimSuccHypTy' Γ P] ->
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tNatElim P hz hs n ≅ tNatElim P' hz' hs' n' : term_decl P[n..]]
      | TermNatElimZero {Γ P hz hs} :
          [Γ ,, tNat |- P ] ->
          [Γ |- hz : term_decl P[tZero..]] ->
          [Γ |- hs : elimSuccHypTy' Γ P] ->
          [Γ |- tNatElim P hz hs tZero ≅ hz : term_decl P[tZero..]]
      | TermNatElimSucc {Γ P hz hs n} :
          [Γ ,, tNat |- P ] ->
          [Γ |- hz : term_decl P[tZero..]] ->
          [Γ |- hs : elimSuccHypTy' Γ P] ->
          [Γ |- n : tNat] ->
          [Γ |- tNatElim P hz hs (tSucc n) ≅ tApp (tApp hs n) (tNatElim P hz hs n) : term_decl P[(tSucc n)..]]
      | TermBoolElimCong {Γ P P' ht ht' hf hf' n n'} :
          [Γ ,, tBool |- P ≅ P'] ->
          [Γ |- ht ≅ ht' : term_decl P[tTrue..]] ->
          [Γ |- hf ≅ hf' : term_decl P[tFalse..]] ->
          [Γ |- n ≅ n' : tBool] ->
          [Γ |- tBoolElim P ht hf n ≅ tBoolElim P' ht' hf' n' : term_decl P[n..]]
      | TermBoolElimTrue {Γ P ht hf} :
          [Γ ,, tBool |- P ] ->
          [Γ |- ht : term_decl P[tTrue..]] ->
          [Γ |- hf : term_decl P[tFalse..]] ->
          [Γ |- tBoolElim P ht hf tTrue ≅ ht : term_decl P[tTrue..]]
      | TermBoolElimFalse {Γ P ht hf} :
          [Γ ,, tBool |- P ] ->
          [Γ |- ht : term_decl P[tTrue..]] ->
          [Γ |- hf : term_decl P[tFalse..]] ->
          [Γ |- tBoolElim P ht hf tFalse ≅ hf : term_decl P[tFalse..]]
      | TermAlphaConv {Γ i n b} :
          [|-Γ] ->
          in_ell (list_at Γ i) n b -> [ Γ |- tApp (tAlpha i) (nat_to_term n) ≅ bool_to_term b : tBool ]
      | TermEmptyElimCong {Γ P P' e e'} :
          [Γ ,, tEmpty |- P ≅ P'] ->
          [Γ |- e ≅ e' : tEmpty] ->
          [Γ |- tEmptyElim P e ≅ tEmptyElim P' e' : term_decl P[e..]]
      | TermLeafCong {Γ} {n n'} :
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tLeaf n ≅ tLeaf n' : tTree]
      | TermNodeCong {Γ} {n n' tl tl' tr tr'} :
          [Γ |- n ≅ n' : tNat] ->
          [Γ |- tl ≅ tl' : tTree] ->
          [Γ |- tr ≅ tr' : tTree] ->
          [Γ |- tNode n tl tr ≅ tNode n' tl' tr' : tTree]
      | TermTreeElimCong {Γ P P' hl hl' hn hn' t t'} :
          [Γ ,, tTree |- P ≅ P'] ->
          [Γ |- hl ≅ hl' : elimLeafHypTy' Γ P] ->
          [Γ |- hn ≅ hn' : elimNodeHypTy' Γ P] ->
          [Γ |- t ≅ t' : tTree] ->
          [Γ |- tTreeElim P hl hn t ≅ tTreeElim P' hl' hn' t' : term_decl P[t..]]
      | TermTreeElimLeaf {Γ P hl hn n} :
          [Γ ,, tTree |- P ] ->
          [Γ |- n : tNat] ->
          [Γ |- hl : elimLeafHypTy' Γ P] ->
          [Γ |- hn : elimNodeHypTy' Γ P] ->
          [Γ |- tTreeElim P hl hn (tLeaf n) ≅ tApp hl n: term_decl P[(tLeaf n)..]]
      | TermTreeElimNode {Γ P hl hn tl tr n} :
          [Γ ,, tTree |- P ] ->
          [Γ |- n : tNat] ->
          [Γ |- hl : elimLeafHypTy' Γ P] ->
          [Γ |- hn : elimNodeHypTy' Γ P] ->
          [Γ |- tl : tTree] ->
          [Γ |- tr : tTree] ->
          [Γ |- tTreeElim P hl hn (tNode n tl tr) ≅
            tApp (tApp (tApp (tApp (tApp hn n) tl) tr) (tTreeElim P hl hn tl)) (tTreeElim P hl hn tr) :
            term_decl P[(tNode n tl tr)..]]
      | TermSigCong {Γ} {A A' B B'} :
          [ Γ |- A : U] ->
          [ Γ |- A ≅ A' : U ] ->
          [ Γ ,, A |- B ≅ B' : U ] ->
          [ Γ |- tSig A B ≅ tSig A' B' : U ]
      | TermPairCong {Γ A A' A'' B B' B'' a a' b b'} :
          [Γ |- A] ->
          [Γ |- A ≅ A'] ->
          [Γ |- A ≅ A''] ->
          [Γ,, A |- B ≅ B'] ->
          [Γ,, A |- B ≅ B''] ->
          [Γ |- a ≅ a' : A] ->
          [Γ |- b ≅ b' : term_decl B[a..]] ->
          [Γ |- tPair A' B' a b ≅ tPair A'' B'' a' b' : tSig A B]
      | TermPairEta {Γ} {A B p} :
          [Γ |- p : tSig A B] ->
          [Γ |- tPair A B (tFst p) (tSnd p) ≅ p : tSig A B]
      | TermFstCong {Γ A B p p'} :
        [Γ |- p ≅ p' : tSig A B] ->
        [Γ |- tFst p ≅ tFst p' : A]
      | TermFstBeta {Γ A B a b} :
        [Γ |- A] ->
        [Γ ,, A |- B] ->
        [Γ |- a : A] ->
        [Γ |- b : term_decl B[a..]] ->
        [Γ |- tFst (tPair A B a b) ≅ a : A]
      | TermSndCong {Γ A B p p'} :
        [Γ |- p ≅ p' : tSig A B] ->
        [Γ |- tSnd p ≅ tSnd p' : term_decl B[(tFst p)..]]
      | TermSndBeta {Γ A B a b} :
        [Γ |- A] ->
        [Γ ,, A |- B] ->
        [Γ |- a : A] ->
        [Γ |- b : term_decl B[a..]] ->
        [Γ |- tSnd (tPair A B a b) ≅ b : term_decl B[(tFst (tPair A B a b))..]]
      | TermIdCong {Γ A A' x x' y y'} :
        (* [Γ |- A] -> ?  *)
        [Γ |- A ≅ A' : U] ->
        [Γ |- x ≅ x' : A] ->
        [Γ |- y ≅ y' : A] ->
        [Γ |- tId A x y ≅ tId A' x' y' : U ]
      | TermReflCong {Γ A A' x x'} :
        [Γ |- A ≅ A'] ->
        [Γ |- x ≅ x' : A] ->
        [Γ |- tRefl A x ≅ tRefl A' x' : tId A x x]
      | TermIdElim {Γ A A' x x' P P' hr hr' y y' e e'} :
        (* Parameters well formed: required for stability by weakening,
          in order to show that the context Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)
          remains well-formed under weakenings *)
        [Γ |- A] ->
        [Γ |- x : A] ->
        [Γ |- A ≅ A'] ->
        [Γ |- x ≅ x' : A] ->
        [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] ->
        [Γ |- hr ≅ hr' : term_decl P[tRefl A x .: x..]] ->
        [Γ |- y ≅ y' : A] ->
        [Γ |- e ≅ e' : tId A x y] ->
        [Γ |- tIdElim A x P hr y e ≅ tIdElim A' x' P' hr' y' e' : term_decl P[e .: y..]]
      | TermIdElimRefl {Γ A x P hr y A' z} :
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
        [Γ |- tIdElim A x P hr y (tRefl A' z) ≅ hr : term_decl P[tRefl A' z .: y..]]
      | TermRefl {Γ} {t A} :
          [ Γ |- t : A ] -> 
          [ Γ |- t ≅ t : A ]
      | TermConv {Γ} {t t' A B : term} :
          [ Γ |- t ≅ t': A ] ->
          [ Γ |- A ≅ B ] ->
          [ Γ |- t ≅ t': B ]
      | TermSym {Γ} {t t' A} :
          [ Γ |- t ≅ t' : A ] ->
          [ Γ |- t' ≅ t : A ]
      | TermTrans {Γ} {t t' t'' A} :
          [ Γ |- t ≅ t' : A ] ->
          [ Γ |- t' ≅ t'' : A ] ->
          [ Γ |- t ≅ t'' : A ]
      | TermSplit {Γ t t' A i new} :
          [|- Γ] ->
          [ Γ,, i : new ↦ true |- t ≅ t' : A] ->
          [ Γ,, i : new ↦ false |- t ≅ t' : A] ->
          [ Γ |- t ≅ t' : A]
      | TermXiCong {Γ t t'} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t ≅ t' : tNat] ->
          [ Γ |- tXi ℓ t ≅ tXi ℓ t' : tTree]
      | TermXiLeaf {Γ n} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ |- tXi ℓ (nat_to_term n) ≅ tLeaf (nat_to_term n) : tTree]
      | TermXiNode {Γ t} {ℓ : ell} {k v} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t : tNat] ->
          whne (ellNe k v) t ->
          [ Γ |- tXi ℓ t ≅ tNode (nat_to_term k) (tXi ℓt t⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tEval ℓ (tBox ℓt (tRel 0)))..])
            (tXi ℓf t⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tEval ℓ (tBox ℓf (tRel 0)))..]) : tTree]
      | TermXXiCong {Γ t t' u u'} {ℓ : ell} :
          [ |- Γ] ->
          [ Γ ,, ℓ |- t ≅ t' : tNat] -> [ Γ |- u ≅ u' : ℓ] ->
          [ Γ |- tXXi ℓ t u ≅ tXXi ℓ t' u' : tId tNat (dEval' Γ (tXi ℓ t) (tEval ℓ u)) t[u..] ]
      | TermXXiLeaf {Γ n u u'} {ℓ : ell} :
          [ |- Γ] -> [ Γ |- u ≅ u' : ℓ] ->
          [ Γ |- tXXi ℓ (nat_to_term n) u ≅ tRefl tNat (nat_to_term n): tId tNat (nat_to_term n) (nat_to_term n) ]
      | TermXXiNode  {Γ m} {ℓ : ell} {k v n} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          whne (ellNe k v) m ->
          [ Γ,, ℓ |- m  : tNat] -> [Γ |- n : ℓ] ->
          [ Γ |- tXXi ℓ m n ≅ tEllElim k ℓ (tId tNat (dEval' (Γ,, ℓ) (tXi ℓ m⟨wk_up ℓ (@wk1 Γ ℓ)⟩) (tEval ℓ (tRel 0))) m)
            (tXXi ℓt m⟨wk_up ℓ (@wk1 Γ ℓt)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓt) ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] (tRel 0))
            (tXXi ℓf m⟨wk_up ℓ (@wk1 Γ ℓf)⟩⟨wk_up ℓ (@wk1 (Γ,,ℓf) ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] (tRel 0))
            n (tApp (tEval ℓ n) (nat_to_term k)):
            tId tNat (dEval' Γ (tXi ℓ m) (tEval ℓ n)) m[n..] ]
      | TermEvalCong {Γ t t'} {ℓ : ell} :
          [ Γ |- t ≅ t' : ℓ ] ->
          [ Γ |- tEval ℓ t ≅ tEval ℓ t' : arr' Γ tNat tBool]
      | TermEvalRel {Γ v n b} {ℓ : ell} :
          [ |- Γ ] ->
          in_ell ℓ n b ->
          [ Γ |- tApp (tEval ℓ (tRel v)) (nat_to_term n) ≅ (bool_to_term b) : tBool]
      | TermEvalBox {Γ ℓ t}:
          [ Γ |- t : arr' Γ tNat tBool] ->
          (forall n b, in_ell (ℓ : ell) n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
          [ Γ |- tEval ℓ (tBox ℓ t) ≅ t : arr' Γ tNat tBool]
      | TermBoxCong {Γ t t'} {ℓ : ell} :
          [ Γ |- t ≅ t' : arr' Γ tNat tBool] ->
          (forall n b, in_ell ℓ n b -> [ Γ |- tApp t (nat_to_term n) ≅ bool_to_term b : tBool]) ->
          [ Γ |- tBox ℓ t ≅ tBox ℓ t' : ℓ]
      | TermEllElimCong {Γ ℓ k} {P P' ht ht' hf hf' n n' b b' : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          [ Γ,, ℓ |- P ≅ P' ] ->
          [ Γ,, ℓt |- ht ≅ ht' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
          [ Γ,, ℓf |- hf ≅ hf' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
          [ Γ |- n ≅ n' : ℓ] -> [Γ |- b ≅ b' : tBool] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
          [ Γ |- tEllElim k ℓ P ht hf n b ≅ tEllElim k ℓ P' ht' hf' n' b' : term_decl P[n..] ]
      | TermEllElimTrue {Γ ℓ k} {P ht hf n : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          [ Γ,, ℓ |- P] ->
          [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
          [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
          [ Γ |- n : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ tTrue : tBool] ->
          [ Γ |- tEllElim k ℓ P ht hf n tTrue ≅ ht[(tBox ℓt (tEval ℓ n))..] : term_decl P[n..]]
      | TermEllElimFalse {Γ ℓ k} {P ht hf n : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
          [ Γ,, ℓ |- P] ->
          [ Γ,, ℓt |- ht : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
          [ Γ,, ℓf |- hf : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
          [ Γ |- n : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ tFalse : tBool] ->
          [ Γ |- tEllElim k ℓ P ht hf n tFalse ≅ hf[(tBox ℓf (tEval ℓ n))..] : term_decl P[n..]]

  where "[   |- Γ ]" := (WfContextDecl Γ)
  and   "[ Γ |- T ]" := (WfTypeDecl Γ T)
  and   "[ Γ |- t : T ]" := (TypingDecl Γ T t)
  and   "[ Γ |- A ≅ B ]" := (ConvTypeDecl Γ A B)
  and   "[ Γ |- t ≅ t' : T ]" := (ConvTermDecl Γ T t t').

  (** (Typed) reduction is defined afterwards,
  rather than mutually with the other relations. *)

  Local Coercion isterm : term >-> class.

  Record RedClosureDecl (Γ : context) (A : class) (t u : term) := {
    reddecl_typ : match A with istype => [Γ |- t] | isterm A => [Γ |- t : A] end;
    reddecl_red : @RedClosureAlg Γ t u;
    reddecl_conv : match A with istype => [ Γ |- t ≅ u ] | isterm A => [Γ |- t ≅ u : A] end;
  }.

  Notation "[ Γ |- t ⤳* t' ∈ A ]" := (RedClosureDecl Γ A t t').

(** ** Declarative neutral conversion *)

(** We have two notions of "convertible neutrals". The first is relatively weak, and says only that
  the two terms are neutral and are convertible (wrt. standard conversion). The good side is that
  it can be shown to satisfy the interface of generic typing already. The bad side is that it does not
  give us strong enough inversion principles. *)

  Record WeakDeclNeutralConversion (Γ : context) (A : decl) (t u : term) := {
    nevar : neVar;
    convnedecl_whne_l : whne nevar t;
    convnedecl_whne_r : whne nevar u;
    convnedecl_conv : [ Γ |- t ≅ u : A ];
  }.

(** The second, much stronger notion compares neutrals only "structurally".
  In particular, it does *not* embed transitivity.
  The price is that at this stage we cannot show that it is transitive, yet – we need injectivity of
  type constructors for that. So we defer that until that later point. *)

  Inductive DeclNeutralConversion (Γ : context) : neVar -> decl -> term -> term -> Type :=

  | neuConvRel (T : term) n : [|- Γ] -> in_ctx Γ n T -> [Γ |- tRel n ~ tRel n : T | termNe]

  | neuConvEval (ℓ : ell) v (k : newnat ℓ) : [|- Γ] -> in_ctx Γ v ℓ ->
    [Γ |- tApp (tEval ℓ (tRel v)) (nat_to_term k) ~ tApp (tEval ℓ (tRel v)) (nat_to_term k) : tBool | ellNe k v]

  | neuConvApp nevar A B n n' a a' :
      [Γ |- n ~ n' : tProd A B | nevar] ->
      [Γ |- a ≅ a' : A] ->
      [Γ |- tApp n a ~ tApp n' a' : term_decl B[a..] | nevar]

  | neuConvNat {nevar P P' hz hz' hs hs' n n'} :
      [Γ |- n ~ n' : tNat | nevar] ->
      [Γ ,, tNat |- P ≅ P'] ->
      [Γ |- hz ≅ hz' : term_decl P[tZero..]] ->
      [Γ |- hs ≅ hs' : elimSuccHypTy' Γ P] ->
      [Γ |- tNatElim P hz hs n ~ tNatElim P' hz' hs' n' : term_decl P[n..] | nevar]

  | neuConvBool {nevar P P' ht ht' hf hf' n n'} :
      [Γ |- n ~ n' : tBool | nevar] ->
      [Γ ,, tBool |- P ≅ P'] ->
      [Γ |- ht ≅ ht' : term_decl P[tTrue..]] ->
      [Γ |- hf ≅ hf' : term_decl P[tFalse..]] ->
      [Γ |- tBoolElim P ht hf n ~ tBoolElim P' ht' hf' n' : term_decl P[n..] | nevar]

  | neuConvAlpha {nevar k i n n'} :
      [Γ |- n ~ n' : tNat | nevar] ->
      [Γ |- tApp (tAlpha i) (nSucc k n) ~ tApp (tAlpha i) (nSucc k n') : tBool | nevar]

  | neuConvEmpty {nevar P P' e e'} :
      [Γ ,, tEmpty |- P ≅ P'] ->
      [Γ |- e ~ e' : tEmpty | nevar] ->
      [Γ |- tEmptyElim P e ~ tEmptyElim P' e' : term_decl P[e..] | nevar]

  | neuConvTree {nevar P P' hl hl' hn hn' t t'} :
      [Γ |- t ~ t' : tTree | nevar] ->
      [Γ ,, tTree |- P ≅ P'] ->
      [Γ |- hl ≅ hl' : elimLeafHypTy' Γ P] ->
      [Γ |- hn ≅ hn' : elimLeafHypTy' Γ P] ->
      [Γ |- tTreeElim P hl hn t ~ tTreeElim P' hl' hn' t' : term_decl P[t..] | nevar]

  | neuConvFst {nevar A B p p'} :
      [Γ |- p ~ p' : tSig A B | nevar] ->
      [Γ |- tFst p ~ tFst p' : A | nevar]

  | neuConvSnd {nevar A B p p'} :
      [Γ |- p ~ p' : tSig A B | nevar] ->
      [Γ |- tSnd p ~ tSnd p' : term_decl B[(tFst p)..] | nevar]

  | neuConvId {nevar A A' x x' P P' hr hr' y y' e e'} :
      [Γ |- A ≅ A'] ->
      [Γ |- x ≅ x' : A] ->
      [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P ≅ P'] ->
      [Γ |- hr ≅ hr' : term_decl P[tRefl A x .: x..]] ->
      [Γ |- y ≅ y' : A] ->
      [Γ |- e ~ e' : tId A x y | nevar] ->
      [Γ |- tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : term_decl P[e .: y..] | nevar]

  | neuConvConv nevar {A B n n' : term} :
      [Γ |- n ~ n' : A | nevar] ->
      [Γ |- A ≅ B] ->
      [Γ |- n ~ n' : B | nevar]

  | neuConvXi nevar {ℓ : ell} {m m' k} :
      [Γ,, ℓ |- m ~ m' : tNat | nevar⟨@wk1 Γ ℓ⟩] ->
      [Γ |- tXi ℓ (nSucc k m) ~ tXi ℓ (nSucc k m') : tTree | nevar]

  | neuConvXXi nevar {ℓ : ell} {m m' n n' k} :
      [Γ |- n ≅ n' : ℓ] ->
      [Γ,, ℓ |- m ~ m' : tNat | nevar⟨@wk1 Γ ℓ⟩] ->
      [Γ |- tXXi ℓ (nSucc k m) n ~ tXXi ℓ (nSucc k m') n' : tId tNat (dEval' Γ (tXi ℓ (nSucc k m)) (tEval ℓ n)) (nSucc k m)[n..] | nevar]

  | neuConEllElim nevar {ℓ k} {P P' ht ht' hf hf' n n' b b' : term} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false):
      [ Γ,, ℓ |- P ≅ P' ] ->
      [ Γ,, ℓt |- ht ≅ ht' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓt)⟩[(tBox ℓ (tEval ℓt (tRel 0)))..] ] ->
      [ Γ,, ℓf |- hf ≅ hf' : term_decl P⟨wk_up ℓ (@wk1 Γ ℓf)⟩[(tBox ℓ (tEval ℓf (tRel 0)))..] ] ->
      [ Γ |- n ≅ n' : ℓ] -> [Γ |- tApp (tEval ℓ n) (nat_to_term k) ≅ b : tBool] ->
      [Γ |- b ~ b' : tBool | nevar] ->
      [Γ |- tEllElim k ℓ P ht hf n b ~ tEllElim k ℓ P' ht' hf' n' b' : term_decl P[n..] | nevar]


  where "[ Γ |- m ~ n : A | nevar ]" := (DeclNeutralConversion Γ nevar A m n).

End Definitions.

Definition TermRedClosure Γ A t u := RedClosureDecl Γ (isterm A) t u.
Definition TypeRedClosure Γ A B := RedClosureDecl Γ istype A B.

Notation "[ Γ |- t ⤳* u ∈ A ]" := (RedClosureDecl Γ A t u).

(** ** Instances *)
(** Used for printing (see Notations) and as a support for the generic typing
properties used for the logical relation (see GenericTyping). *)
Module DeclarativeTypingData.

  Definition de : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Decl : WfContext de := WfContextDecl.
  #[export] Instance WfType_Decl : WfType de := WfTypeDecl.
  #[export] Instance Typing_Decl : Typing de := TypingDecl.
  #[export] Instance ConvType_Decl : ConvType de := ConvTypeDecl.
  #[export] Instance ConvTerm_Decl : ConvTerm de := ConvTermDecl.
  #[export] Instance RedType_Decl : RedType de := TypeRedClosure.
  #[export] Instance RedTerm_Decl : RedTerm de := TermRedClosure.
  #[export] Instance ConvNeuConv_Decl : ConvNeuConv de := fun nevar Γ => DeclNeutralConversion Γ nevar.

  Ltac fold_decl :=
    change WfContextDecl with (wf_context (ta := de)) in * ;
    change WfTypeDecl with (wf_type (ta := de)) in *;
    change TypingDecl with (typing (ta := de)) in * ;
    change ConvTypeDecl with (conv_type (ta := de)) in * ;
    change ConvTermDecl with (conv_term (ta := de)) in * ;
    change TypeRedClosure with (red_ty (ta := de)) in *;
    change TermRedClosure with (red_tm (ta := de)) in *;
    change DeclNeutralConversion with (conv_neu_ty (ta := de)) in *.

  Smpl Add fold_decl : refold.

End DeclarativeTypingData.

(** This weaker instance is necessary to break circularity: indeed, we can only derive
  that the above instance is an instance of generic typing once we have injectivity
  of type constructors, because we need said injectivity to show that neutral conversion
  is transitive. So we will first instantiate the logical relation once with this
  weaker instance, obtain injectivity of type constructors, then derive that the above
  instance is also an instance of generic typing, then instantiate the logical relation again.
*)
Module WeakDeclarativeTypingData.

  Import DeclarativeTypingData.
  #[export] Remove Hints DeclNeutralConversion : typeclass_instances.
  #[export] Instance ConvNeuConv_WeakDecl : ConvNeuConv de := WeakDeclNeutralConversion.

End WeakDeclarativeTypingData.

Import DeclarativeTypingData.

(** ** Induction principles *)

(** We use Scheme to generate mutual induction principle. Sadly, Scheme uses
the product of the standard library, which is not universe polymorphic, which
causes universe issues, typically in the fundamental lemma. So
we use some Ltac code to generate properly polymorphic versions of the inductive
principle. We also use Ltac to generate the conclusion of the mutual induction
proof, to alleviate the user from the need to write it down every time: they
only need write the predicates to be proven. *)
Section InductionPrinciples.

Scheme 
    Minimality for WfContextDecl Sort Type with
    Minimality for WfTypeDecl   Sort Type with
    Minimality for TypingDecl    Sort Type with
    Minimality for ConvTypeDecl  Sort Type with
    Minimality for ConvTermDecl  Sort Type.

Combined Scheme _WfDeclInduction from
    WfContextDecl_rect_nodep,
    WfTypeDecl_rect_nodep,
    TypingDecl_rect_nodep,
    ConvTypeDecl_rect_nodep,
    ConvTermDecl_rect_nodep.

Let _WfDeclInductionType :=
  ltac:(let ind := fresh "ind" in
      pose (ind := _WfDeclInduction);
      refold ;
      let ind_ty := type of ind in
      exact ind_ty).

Let WfDeclInductionType :=
  ltac: (let ind := eval cbv delta [_WfDeclInductionType] zeta
    in _WfDeclInductionType in
    let ind' := polymorphise ind in
  exact ind').

Lemma WfDeclInduction : WfDeclInductionType.
Proof.
  intros PCon PTy PTm PTyEq PTmEq **.
  pose proof (_WfDeclInduction PCon PTy PTm PTyEq PTmEq) as H.
  destruct H as [?[?[? []]]].
  all: try (assumption ; fail).
  repeat (split;[assumption|]); assumption.
Qed.

Definition WfDeclInductionConcl :=
  ltac:(
    let t := eval cbv delta [WfDeclInductionType] beta in WfDeclInductionType in
    let t' := remove_steps t in
    exact t').

End InductionPrinciples.

Arguments WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq : rename.

Lemma wfTermAppArr {Γ} {f a A B : term} :
  [ Γ |- f : arr A B ] -> [ Γ |- a : A ] -> 
  [ Γ |- tApp f a : B ].
Proof.
  intros Hf Ha.
  rewrite <- (@shift_subst1' B a).
  now eapply wfTermApp.
Qed.
Lemma TermAppArrCong {Γ} {a b f g A B : term} :
          [ Γ |- f ≅ g : arr A B ] ->
          [ Γ |- a ≅ b : A ] ->
          [ Γ |- tApp f a ≅ tApp g b : B ].
Proof.
  intros Hfg Hab.
  rewrite <- (@shift_subst1' B a).
  now eapply TermAppCong.
Qed.

Print Instances Subst1.

(* 
(** ** Generation *)

(** The generation lemma (the name comes from the PTS literature), gives a 
stronger inversion principle on typing derivations, that give direct access
to the last non-conversion rule, and bundle together all conversions.

Note that because we do not yet know that [Γ |- t : T] implies [Γ |- T],
we cannot use reflexivity in the case where the last rule was not a conversion
one, and we get the slightly clumsy disjunction of either an equality or a
conversion proof. We get a better version of generation later on, once we have
this implication. *)

Definition termGenData (Γ : context) (t T : term) : Type :=
  match t with
    | tRel n => ∑ decl, [× T = decl, [|- Γ]& in_ctx Γ n decl]
    | tProd A B =>  [× T = U, [Γ |- A : U] & [Γ,, A |- B : U]]
    | tLambda A t => ∑ B, [× T = tProd A B, [Γ |- A] & [Γ,, A |- t : B]]
    | tApp f a => ∑ A B, [× T = B[a..], [Γ |- f : tProd A B] & [Γ |- a : A]]
    | tSort _ => False
    | tNat => T = U
    | tZero => T = tNat
    | tSucc n => T = tNat × [Γ |- n : tNat]
    |  tNatElim P hz hs n =>
      [× T = P[n..], [Γ,, tNat|- P], [Γ |- hz : P[tZero..]], [Γ |- hs : elimSuccHypTy P] & [Γ |- n : tNat]]
    | tBool => T = U
    | tTrue => T = tBool
    | tFalse => T = tBool
    | tBoolElim P ht hf b =>
      [× T = P[b..], [Γ,, tBool |- P], [Γ |- ht : P[tTrue..]], [Γ |- hf : P[tFalse..]] & [Γ |- b : tBool]]
    | tTree => T = U
    | tLeaf n => T = tTree × [Γ |- n : tNat]
    | tNode n tl tr => T = tTree × [Γ |- n : tNat] × [Γ |- tl : tTree] × [Γ |- tr : tTree]
    |  tTreeElim P hl hn t =>
      [× T = P[t..], [Γ,, tTree|- P], [Γ |- hl : elimLeafHypTy P], [Γ |- hn : elimNodeHypTy P] & [Γ |- t : tTree]]
    | tAlpha i => T = arr tNat tBool
    | tEmpty => T = U
    | tEmptyElim P e =>
      [× T = P[e..], [Γ,, tEmpty |- P] & [Γ |- e : tEmpty]]
    | tSig A B => [× T = U, [Γ |- A : U] & [Γ ,, A |- B : U]]
    | tPair A B a b =>
     [× T = tSig A B, [Γ |- A], [Γ,, A |- B], [Γ |- a : A] & [Γ |- b : B[a..]]]
    | tFst p => ∑ A B, T = A × [Γ |- p : tSig A B]
    | tSnd p => ∑ A B, T = B[(tFst p)..] × [Γ |- p : tSig A B]
    | tId A x y => [× T = U, [Γ |- A : U], [Γ |- x : A] & [Γ |- y : A]]
    | tRefl A x => [× T = tId A x x, [Γ |- A] & [Γ |- x : A]]
    | tIdElim A x P hr y e => 
      [× T = P[e .: y..], [Γ |- A], [Γ |- x : A], [Γ,, A,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |- P], [Γ |- hr : P[tRefl A x .: x..]], [Γ |- y : A] & [Γ |- e : tId A x y]]
  end.




Lemma termGenSplit Γ t A i new :
  termGenData (Γ,, i : new ↦ true) t A ->
  termGenData (Γ,, i : new ↦ false) t A ->
  termGenData Γ t A.
Proof.
  intros Ht Hf.
  induction t.
  all: cbn in *.
  + destruct Ht as [? [<- wt in_t]].
    destruct Hf as [? [<- wf in_f]].
    eexists ; split.
    reflexivity. 2: eapply in_f.
    now eapply consplit.
    apply in_f.
  + apply Ht.
  + destruct Ht as [-> Ht1 Ht2].
    destruct Hf as [_ Hf1 Hf2].
    prod_splitter.
    reflexivity.
    now eapply wfTermSplit.
    now eapply wfTermSplit.
  + destruct Ht as [? [-> Ht1 Ht2]].
    destruct Hf as [B [e Hf1 Hf2]].
    inversion e; subst.
    prod_splitter.
    reflexivity.
    now eapply wfTypeSplit.
    now eapply wfTermSplit.
Admitted.

(* Use `termGen` from later on instead after this file. *)
Lemma _termGen Γ t A :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' ≅ A]).
Proof.
  induction 1.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).
  + destruct IHTypingDecl as [? [? [-> | ]]].
    * prod_splitter; tea; now right.
    * prod_splitter; tea; right; now eapply TypeTrans.
  + destruct IHTypingDecl1 as [? [? [ -> | ]]], IHTypingDecl2 as [? [? [ -> | ]]].
    * prod_splitter.
      now eapply termGenSplit.
      left; reflexivity.
    * prod_splitter.
Qed.

Lemma prod_ty_inv Γ A B :
  [Γ |- tProd A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  inversion Hty ; subst ; refold.
  - easy.
  - eapply _termGen in H as (?&[]&_) ; subst.
    split ; now econstructor.
Qed.

Lemma sig_ty_inv Γ A B :
  [Γ |- tSig A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  inversion Hty ; subst ; refold.
  - easy.
  - eapply _termGen in H as (?&[]&_) ; subst.
    split ; now econstructor.
Qed.

Lemma id_ty_inv Γ A x y :
  [Γ |- tId A x y] ->
  [× [Γ |- A], [Γ |- x : A] & [Γ |- y : A]].
Proof.
  intros Hty.
  inversion Hty ; subst ; refold.
  - easy.
  - eapply _termGen in H as (?&[]&_) ; subst.
    split ; try easy ; now econstructor.
Qed.

Lemma neutral_ty_inv Γ A :
  [Γ |- A] -> whne A -> [Γ |- A : U].
Proof.
  intros Hty Hne.
  inversion Hty ; subst ; refold.
  1-7: inversion Hne.
  easy.
Qed. *)
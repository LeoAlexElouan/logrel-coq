(** * LogRel.Syntax.NormalForms: definition of normal and neutral forms, and properties. *)
From Stdlib Require Import ssrbool Logic.StrictProp.
From Equations Require Import Equations. (* for depelim *)
From LogRel Require Import AutoSubst.Extra Utils.
From LogRel.Syntax Require Import BasicAst Context Computations.

(** ** Weak-head normal forms and neutrals. *)
Variant neVar := termNe | ellNe (k v : nat).
Instance Ren1_neVar : Ren1 (nat -> nat) neVar neVar := fun ρ nevar =>
  match nevar with
  | termNe => termNe
  | ellNe k v => ellNe k (ρ v)
  end.
Equations Derive NoConfusion for neVar.

(* Inductive whns {k v : nat} : term -> Type :=
  | whns_tEval {ℓ} : notin_ell (ℓ : ell) k -> whns (tApp (tEval ℓ (tRel v)) (nat_to_term k))
  | whns_tApp {n t} : whns n -> whns (tApp n t)
  | whns_tNatElim {P hz hs n} : whns n -> whns (tNatElim P hz hs n)
  | whns_tBoolElim {P ht hf n} : whns n -> whns (tBoolElim P ht hf n)
  | whns_tEmptyElim {P e} : whns e -> whns (tEmptyElim P e)
  | whns_tTreeElim {P hl hn n} : whns n -> whns (tTreeElim P hl hn n)
  | whns_tFst {p} : whns p -> whns (tFst p)
  | whns_tSnd {p} : whns p -> whns (tSnd p)
  | whns_tIdElim {A x P hr y e} : whns e -> whns (tIdElim A x P hr y e)
  | whns_tAlpha {i t n} : whns t -> whns (tApp (tAlpha i) (nSucc n t))
  | whns_tXi {n ℓ k'} : whns (v := S v) n -> whns (tXi ℓ (nSucc k' n))
  | whns_tXXi {m n ℓ k'} : whns (v := S v) m -> whns (tXXi ℓ (nSucc k' m) n)
  | whns_tEllElim kℓ ℓ P ht hf n b : whns b -> whns (tEllElim kℓ ℓ P ht hf n b).
Arguments whns : clear implicits.
 *)
Inductive whne : neVar -> term -> Type :=
  | whne_tRel {v} : whne termNe (tRel v)
  | whns_tEval {ℓ k v} : notin_ell (ℓ : ell) k -> whne (ellNe k v) (tApp (tEval ℓ (tRel v)) (nat_to_term k))
  | whne_tApp {n t nevar} : whne nevar n -> whne nevar (tApp n t)
  | whne_tNatElim {P hz hs n nevar} : whne nevar n -> whne nevar (tNatElim P hz hs n)
  | whne_tBoolElim {P ht hf n nevar} : whne nevar n -> whne nevar (tBoolElim P ht hf n)
  | whne_tEmptyElim {P e nevar} : whne nevar e -> whne nevar (tEmptyElim P e)
  | whne_tTreeElim {P hl hn n nevar} : whne nevar n -> whne nevar (tTreeElim P hl hn n)
  | whne_tFst {p nevar} : whne nevar p -> whne nevar (tFst p)
  | whne_tSnd {p nevar} : whne nevar p -> whne nevar (tSnd p)
  | whne_tIdElim {A x P hr y e nevar} : whne nevar e -> whne nevar (tIdElim A x P hr y e)
  | whne_tAlpha {i t k nevar} : whne nevar t -> whne nevar (tApp (tAlpha i) (nSucc k t))
  | whne_tXi {n ℓ k nevar} : whne nevar⟨↑⟩ n -> whne nevar (tXi ℓ (nSucc k n))
  | whne_tXXi {m n ℓ k nevar} : whne nevar⟨↑⟩ m -> whne nevar (tXXi ℓ (nSucc k m) n)
  | whne_tEllElim {kℓ ℓ P ht hf n b nevar} : whne nevar b -> whne nevar (tEllElim kℓ ℓ P ht hf n b).

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tAlpha {i} : whnf (tAlpha i)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tBool : whnf tBool
  | whnf_tTrue : whnf tTrue
  | whnf_tFalse : whnf tFalse
  | whnf_tEmpty : whnf tEmpty
  | whnf_tTree : whnf tTree
  | whnf_tLeaf {n} : whnf (tLeaf n)
  | whnf_tNode {n tl tr} : whnf (tNode n tl tr)
  | whnf_tSig {A B} : whnf (tSig A B)
  | whnf_tPair {A B a b} : whnf (tPair A B a b)
  | whnf_tId {A x y} : whnf (tId A x y)
  | whnf_tRefl {A x} : whnf (tRefl A x)
  | whnf_whne {nevar n} : whne nevar n -> whnf n.

#[global] Hint Constructors whne whnf : gen_typing.

(* Equations Derive Signature for whns. *)
Equations Derive Signature for whne.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

#[local] Ltac nSucc_handler :=
try match goal with
| eq : nSucc ?k ?t = nSucc ?k' ?t' |- _ =>
    eapply nSucc_eq_inv in eq as [[<- <-] | [(?&->&<-)|(?&<-&->)]]
| eq : nSucc ?k ?t  = nat_to_term ?k' |- _ =>
    eapply eq_sym, nSucc_nat_to_term in eq as [[] <-]
| eq : nat_to_term ?k = nSucc ?k' ?t' |- _ =>
    eapply nSucc_nat_to_term in eq as [[] <-]
| eq  : nat_to_term ?k =  nat_to_term ?k' |- _ =>
    eapply nat_to_term_inj in eq as <-
end.

Lemma nevar_uniq {n nevar nevar'} : whne nevar n -> whne nevar' n -> nevar = nevar'.
Proof.
  intros ne ne'.
  induction ne in nevar', ne' |-*; inversion ne'; subst; clear ne'; nSucc_handler; eauto.
  all: try solve [inversion H1 | inversion ne].
  all: specialize (IHne _ H1);
    destruct nevar, nevar';
     inversion IHne; subst; clear IHne;
     reflexivity.
Qed.

Section neNotne.
  Context (nevar : neVar).

  Lemma neSort s : whne nevar (tSort s) -> False.
  Proof.
    inversion 1.
  Qed.

  Lemma nePi A B : whne nevar (tProd A B) -> False.
  Proof.
    inversion 1.
  Qed.

  Lemma neLambda A t : whne nevar (tLambda A t) -> False.
  Proof.
    inversion 1.
  Qed.
End neNotne.

(* Lemma whne_tAlphanSucc {i t n} : whne t -> whne (tApp (tAlpha i) (nSucc n t)).
Proof.
  intros hne.
  induction n.
  + now constructor.
  + now (apply whne_tAlphaSucc).
Qed.
 *)
(* #[global] Hint Resolve neSort nePi neLambda : gen_typing. *)

(** ** Restricted classes of normal forms *)

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | BoolType : isType tBool
  | EmptyType : isType tEmpty
  | TreeType : isType tTree
  | SigType {A B} : isType (tSig A B)
  | IdType {A x y} : isType (tId A x y)
  | NeType {A nevar}  : whne nevar A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | BoolPos : isPosType tBool
  | EmptyPos : isPosType tEmpty
  | TreePos : isPosType tTree
  | IdPos {A x y} : isPosType (tId A x y)
  | NePos {A nevar}  : whne nevar A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | AlphaFun {i} : isFun (tAlpha i)
  | NeFun {f nevar} : whne nevar f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n nevar} : whne nevar n -> isNat n.

Inductive isBool : term -> Type :=
  | TrueBool : isBool tTrue
  | FalseBool : isBool tFalse
  | NeBool {n nevar} : whne nevar n -> isBool n.

Inductive isTree : term -> Type :=
  | LeafTree {n} : isTree (tLeaf n)
  | NodeTree {n tl tr} : isTree (tNode n tl tr)
  | NeTree {n nevar} : whne nevar n -> isTree n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p nevar} : whne nevar p -> isPair p.

Inductive isId : term -> Type :=
  | ReflId {A a} : isId (tRefl A a)
  | NeId {n nevar} : whne nevar n -> isId n.

Definition isPosType_isType t (i : isPosType t) : isType t.
Proof. destruct i; now econstructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now econstructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now econstructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now econstructor. Defined.

Coercion isPair_whnf : isPair >-> whnf.

Definition isNat_whnf t (i : isNat t) : whnf t :=
  match i with
  | ZeroNat => whnf_tZero
  | SuccNat => whnf_tSucc
  | NeNat n => whnf_whne n
  end.

Definition isBool_whnf t (i : isBool t) : whnf t :=
  match i with
  | TrueBool => whnf_tTrue
  | FalseBool => whnf_tFalse
  | NeBool n => whnf_whne n
  end.

Definition isTree_whnf t (i : isTree t) : whnf t :=
  match i with
  | LeafTree => whnf_tLeaf
  | NodeTree => whnf_tNode
  | NeTree n => whnf_whne n
  end.

Definition isId_whnf t (i : isId t) : whnf t :=
  match i with
  | ReflId => whnf_tRefl
  | NeId n => whnf_whne n
  end.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isTree_whnf isPair_whnf isId_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isBool isTree isId : gen_typing.

Equations Derive Signature for isNat.

Lemma isNat_zero (n : isNat tZero) : n = ZeroNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isNat_succ t (n : isNat (tSucc t)) : n = SuccNat.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.


Lemma isNat_ne t (n : isNat t) nevar : whne nevar t -> ∑ w, n = NeNat (nevar:=nevar) w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
  destruct (nevar_uniq w w0).
  now eexists.
Qed.

Equations Derive Signature for isBool.

Lemma isBool_true (n : isBool tTrue) : n = TrueBool.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isBool_false (n : isBool tFalse) : n = FalseBool.
Proof.
  depelim n.
  1: easy.
  inversion w.
Qed.

Lemma isBool_ne t (n : isBool t) nevar : whne nevar t -> ∑ w, n = NeBool (nevar:=nevar) w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
  destruct (nevar_uniq w w0).
  now eexists.
Qed.

Derive Signature for isId.

Lemma isId_refl A a (n : isId (tRefl A a)) : n = ReflId.
Proof.
  depelim n.
  1: reflexivity.
  inversion w ; cbn ; easy.
Qed.

Lemma isId_ne t (n : isId t) nevar : whne nevar t -> ∑ w, n = NeId (nevar:=nevar) w.
Proof.
  intros w.
  dependent inversion n ; subst.
  1: inversion w.
  destruct (nevar_uniq w w0).
  now eexists.
Qed.

(** * Unicity of witnesses *)

Lemma whne_nSucc {t t' k k' nevar} : whne nevar t -> whne nevar t' -> nSucc k t = nSucc k' t' -> t = t' /\ k = k'.
Proof.
  intros net net' [[<- <-]| [(n'&->&<-)|(n&<-&->)]]%nSucc_eq_inv.
  + easy.
  + inversion net.
  + inversion net'.
Qed.



Definition whne_uniq {t nevar} (w1 w2 : whne nevar t) : w1 = w2.
Proof.
  induction w1.
  all: try depelim w2; eauto.
  all: try solve [f_equal; eauto | inversion w1 | inversion w2].
  + assert (e = eq_refl) as -> by
      (enough (uip : UIP term) by eapply uip; typeclasses eauto).
    assert (H = eq_refl) as -> by
      (enough (uip : UIP _) by eapply uip; typeclasses eauto).
    cbn in H0. eauto.
  + destruct (whne_nSucc w1 w2 e) as [<- <-].
    assert (e = eq_refl) as -> by
      (enough (uip : UIP term) by eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    f_equal; eauto.
  + destruct (whne_nSucc w1 w2 e) as [<- <-].
    assert (e = eq_refl) as -> by
      (enough (uip : UIP term) by eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    f_equal; eauto.
  + destruct (whne_nSucc w1 w2 e') as [<- <-].
    assert (e' = eq_refl) as -> by
      (enough (uip : UIP term) by eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    f_equal; eauto.
Qed.

Derive Signature for isType.

Definition isType_uniq {A} (w1 w2 : isType A) : w1 = w2.
Proof.
  destruct w1; depelim w2; try reflexivity; try solve [inv_whne].
  destruct (nevar_uniq w w0).
  f_equal; now eapply whne_uniq.
Qed.

Lemma isNat_uniq {t} (p q : isNat t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  destruct (nevar_uniq w w0).
  f_equal; eapply whne_uniq.
Qed.

Lemma isBool_uniq {t} (p q : isBool t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  destruct (nevar_uniq w w0).
  f_equal; eapply whne_uniq.
Qed.

Lemma isId_uniq {t} (p q : isId t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  destruct (nevar_uniq w w0).
  f_equal; eapply whne_uniq.
Qed. 


(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tAlpha {i} : isCanonical (tAlpha i)
  | can_tNat : isCanonical tNat
  | can_tZero : isCanonical tZero
  | can_tSucc {n} : isCanonical (tSucc n)
  | can_tBool : isCanonical tBool
  | can_tTrue : isCanonical tTrue
  | can_tFalse : isCanonical tFalse
  | can_tEmpty : isCanonical tEmpty
  | can_tTree : isCanonical tTree
  | can_tLeaf {n} : isCanonical (tLeaf n)
  | can_tNode {n tl tr} : isCanonical (tNode n tl tr)
  | can_tSig {A B} : isCanonical (tSig A B)
  | can_tPair {A B a b}: isCanonical (tPair A B a b)
  | can_tId {A x y}: isCanonical (tId A x y)
  | can_tRefl {A x}: isCanonical (tRefl A x).

#[global] Hint Constructors isCanonical : gen_typing.

Lemma can_whne_exclusive t nevar : isCanonical t -> whne nevar t -> False.
Proof.
  intros Hcan Hne.
  inversion Hcan ; subst ; inversion Hne.
Qed.

Lemma whnf_can_whne t : whnf t <~> isCanonical t + {nevar & whne nevar t}.
Proof.
  split.
  - intros [].
    all: try solve [left; now constructor | now right].
  - intros [[]|[]]; try now repeat econstructor.
Qed.

Lemma not_can_whne t : whnf t -> ¬ isCanonical t -> {nevar & whne nevar t}.
Proof.
  intros []%whnf_can_whne; eauto.
  now intros [].
Qed.

Lemma not_whne_can t : whnf t -> ¬ {nevar & whne nevar t} -> isCanonical t.
Proof.
  intros []%whnf_can_whne ; eauto.
  now intros [].
Qed.

(** ** Stacks *)
(** A representation of evaluation contexts as lists of destructors with a hole.
  A neutral is exactly a variable in an evaluation context. *)

Variant dest_entry : Type :=
| eEmptyElim (P : term)
| eNatElim (P : term) (hs hz : term)
| eBoolElim (P : term) (ht hf : term)
| eApp (u : term)
| eFst
| eSnd
| eIdElim (A x P hr y : term).

Definition zip1 (t : term) (e : dest_entry) : term :=
match e with
  | eEmptyElim P => (tEmptyElim P t)
  | eNatElim P hs hz => (tNatElim P hs hz t)
  | eBoolElim P hs hz => (tBoolElim P hs hz t)
  | eApp u => (tApp t u)
  | eFst => tFst t
  | eSnd => tSnd t
  | eIdElim A x P hr y => tIdElim A x P hr y t
end.

Definition stack := list dest_entry.

Fixpoint zip t (π : stack) :=
match π with
| nil => t
| cons s π => zip (zip1 t s) π
end.

Variant ty_entry : term -> Type :=
| eSort s : ty_entry (tSort s)
| eProd A B : ty_entry (tProd A B)
| eNat : ty_entry tNat
| eBool : ty_entry tBool
| eEmpty : ty_entry tEmpty
| eTree : ty_entry tTree
| eSig A B : ty_entry (tSig A B)
| eId A x y : ty_entry (tId A x y).

Variant nat_entry : term -> Type :=
| eZero : nat_entry tZero
| eSucc t : nat_entry (tSucc t).

Variant bool_entry : term -> Type :=
| eTrue : bool_entry tTrue
| eFalse : bool_entry tFalse.

Variant tree_entry : term -> Type :=
| eLeaf n : tree_entry (tLeaf n)
| eNode n tl tr : tree_entry (tNode n tl tr).

(** ** Normal and neutral forms are stable by renaming *)

Section RenWhnf.

Lemma ren_nSucc_inv {ρ k t t'} : nSucc k t = t'⟨ρ⟩ -> {u | t = u⟨ρ⟩ /\ t' = nSucc k u}.
Proof.
  induction k as [|k] in ρ, t, t' |-*; cbn.
  + intros ->. now exists t'.
  + intros e.
    destruct t'; cbn in *; try solve [congruence].
    inversion e as [e']; clear e.
    specialize (IHk _ _ _ e').
    destruct IHk as [ u [-> ->]].
    now exists u.
Qed.


  #[local] Ltac push_renaming :=
  (* repeat *) match goal with
  | eq : _ = ?t⟨_⟩ |- _ =>
      destruct t ; cbn in * ; try solve [congruence] ;
      inversion eq ; subst ; clear eq
  end.

  Variable (ρ (* ρε *): nat -> nat).

  Lemma whne_ren t nevar : whne nevar t -> whne nevar⟨ρ⟩ t⟨ρ⟩. (* whne nevar⟨ρ⟩ t⟨ρ⟩ <~> whne nevar t. *)
  Proof.
  induction 1 in ρ |-*; cbn.
  2: unfold nat_to_term.
  2,11-13 : rewrite nSucc_ren.
  all: try now econstructor.
  + econstructor.
    specialize (IHwhne (upRen_term_term ρ)).
    destruct nevar; eapply IHwhne.
  + econstructor.
    specialize (IHwhne (upRen_term_term ρ)).
    destruct nevar; eapply IHwhne.
(*     split.
    - remember t⟨ρ⟩ as t'.
      remember nevar⟨ρ⟩ as nevar'.
      intros Hne.
      induction Hne in ρ, t, Heqt', nevar, Heqnevar' |- * ; cbn.
      1,3-10: try (repeat push_renaming; econstructor ; now eauto).
      + push_renaming.
        push_renaming.
        eapply ren_nSucc_inv in H1
          as [u [? ->]].
        push_renaming.
        push_renaming.
        push_renaming.
        now eapply whne_tAlpha, IHHne.
      + push_renaming.
        eapply ren_nSucc_inv in H1 as [u [-> ->]].
        now eapply whne_tXi, IHHne.
      + push_renaming.
        eapply ren_nSucc_inv in H1 as [u [-> ->]].
        now eapply whne_tXXi, IHHne.
      + push_renaming.
        eapply ren_nSucc_inv in H1 as [u [-> ->]].
        eapply whne_tXXiRed; tea. , IHHne.
      + push_renaming.
        eapply ren_nSucc_inv in H1 as [u [H1 ->]].
        do 3 push_renaming.
        now eapply whne_tEval. *)
  Qed.

  Lemma whnf_ren t : whnf t -> whnf t⟨ρ⟩. 
  Proof.
    induction 1; cbn.
    all: econstructor.
    now eapply whne_ren.
(*     split.
    - remember t⟨ρ⟩ as t'.
      intros Hnf.
      induction Hnf in t, Heqt' |- * ; cbn.
      1-19: push_renaming ; econstructor ; eauto.
      1-13: try now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
 *)  Qed.

(*   Lemma isType_ren A : isType (A⟨ρ⟩) <~> isType A.
  Proof.
    split.
    - remember A⟨ρ⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A : isPosType (A⟨ρ⟩) <~> isPosType A.
  Proof.
    split.
    - remember A⟨ρ⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isFun_ren f : isFun (f⟨ρ⟩) <~> isFun f.
  Proof.
    split.
    - remember f⟨ρ⟩ as f'.
      intros Hfun.
      induction Hfun in f, Heqf' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.


  Lemma isPair_ren p : isPair (p⟨ρ⟩) <~> isPair p.
  Proof.
    split.
    - remember p⟨ρ⟩ as p'.
      intros Hpair.
      induction Hpair in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isId_ren p : isId (p⟨ρ⟩) <~> isId p.
  Proof.
    split.
    - remember p⟨ρ⟩ as p'.
      intros Hid.
      induction Hid in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed. *)

  Lemma isCanonical_ren t : isCanonical (t⟨ρ⟩) <~> isCanonical t.
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: now econstructor.
  Qed.

End RenWhnf.

(* #[global] Hint Constructors isCanonical : gen_typing.
#[global] Hint Constructors whne whnf : gen_typing.
#[global] Hint Resolve neSort nePi neLambda : gen_typing.
#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isTree_whnf isPair_whnf isId_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isBool isTree isId : gen_typing. *)
#[global] Hint Resolve whne_ren whnf_ren (* isType_ren isPosType_ren isFun_ren isId_ren *) isCanonical_ren : gen_typing.
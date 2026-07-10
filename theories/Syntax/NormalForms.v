(** * LogRel.Syntax.NormalForms: definition of normal and neutral forms, and properties. *)
From Stdlib Require Import ssrbool Logic.StrictProp.
From Equations Require Import Equations. (* for depelim *)
From LogRel Require Import AutoSubst.Extra Utils.
From LogRel.Syntax Require Import BasicAst Context Computations.

(** ** Weak-head normal forms and neutrals. *)

(* Instance Ren1_neVar : Ren1 (nat -> nat) neVar neVar := fun ρ nevar =>
  match nevar with
  | termNe => termNe
  | ellNe k v => ellNe k (ρ v)
  end.
Instance RenAlpha_neVar : RenAlpha neVar := fun _ nevar => nevar.
Equations Derive NoConfusion for neVar.
 *)
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

Fixpoint term_under_nSucc {A} (k : nat -> term -> A) n t {struct t} : A :=
match t with
  | tSucc t => term_under_nSucc k (S n) t
  | _ => k n t
end.

Definition headEval v head (k : nat) (t : term) : option (nat × nat) :=
  match t with tZero => Some (k, v) | _ => head t end.
Definition headAlpha head (n : nat) (t : term) : option (nat × nat) := head t.

Definition headXi_aux (o : option (nat × nat)) := match o with
  Some (k, S v) => Some (k, v) |_ => None end.
Definition headXi head (n : nat) (t : term) : option (nat × nat) := headXi_aux (head t).

Fixpoint head (t : term) : option (nat × nat) :=
  match t with
 | tApp (tEval _ (tRel v)) t => term_under_nSucc (headEval v head) 0 t
 | tApp (tAlpha _) t => term_under_nSucc (headAlpha head) 0 t
 | tXi _ t
 | tXXi _ t _ => term_under_nSucc (headXi head) 0 t
 | tNatElim _ _ _ t
 | tBoolElim _ _ _ t
 | tEmptyElim _ t
 | tTreeElim _ _ _ t
 | tFst t
 | tSnd t
 | tIdElim _ _ _ _ _ t
 | tEllElim _ _ _ _ _ _ t => head t
 | _ => None
end.




Inductive whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tEvalRel {ℓ k v} : notin_ell (ℓ : ell) k -> whne (tApp (tEval ℓ (tRel v)) (nat_to_term k))
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tBoolElim {P ht hf n} : whne n -> whne (tBoolElim P ht hf n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tTreeElim {P hl hn n} : whne n -> whne (tTreeElim P hl hn n)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
  | whne_tIdElim {A x P hr y e} : whne e -> whne (tIdElim A x P hr y e)
  | whne_tAlpha {i t k} : whne t -> whne (tApp (tAlpha i) (nSucc k t))
  | whne_tEval {t ℓ v k} : whne t -> whne (tApp (tEval ℓ (tRel v)) (nSucc k t))
  | whne_tXi {n ℓ v kv k} : whne n -> head n = Some (kv, S v) -> whne (tXi ℓ (nSucc k n))
  | whne_tXXi {m n ℓ v kv k} : whne m -> head m = Some (kv, S v) -> whne (tXXi ℓ (nSucc k m) n)
  | whne_tEllElim {kℓ ℓ P ht hf n b} : whne b -> whne (tEllElim kℓ ℓ P ht hf n b).

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tAlpha {i} : whnf (tAlpha i)
  | whnf_tEval {ℓ v} : whnf (tEval ℓ (tRel v))
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
  | whnf_whne {n} : whne n -> whnf n.

#[global] Hint Constructors whne whnf : gen_typing.

(* Equations Derive Signature for whns. *)
Equations Derive Signature for whne.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
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


Section neNotne.

  Lemma neSort s : whne (tSort s) -> False.
  Proof.
    inversion 1.
  Qed.

  Lemma nePi A B : whne (tProd A B) -> False.
  Proof.
    inversion 1.
  Qed.

  Lemma neLambda A t : whne (tLambda A t) -> False.
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
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | BoolPos : isPosType tBool
  | EmptyPos : isPosType tEmpty
  | TreePos : isPosType tTree
  | IdPos {A x y} : isPosType (tId A x y)
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | AlphaFun {i} : isFun (tAlpha i)
  | EvalFun {ℓ v} : isFun (tEval ℓ (tRel v))
  | NeFun {f} : whne f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n} : whne n -> isNat n.

Inductive isBool : term -> Type :=
  | TrueBool : isBool tTrue
  | FalseBool : isBool tFalse
  | NeBool {n} : whne n -> isBool n.

Inductive isTree : term -> Type :=
  | LeafTree {n} : isTree (tLeaf n)
  | NodeTree {n tl tr} : isTree (tNode n tl tr)
  | NeTree {n} : whne n -> isTree n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p} : whne p -> isPair p.

Inductive isId : term -> Type :=
  | ReflId {A a} : isId (tRefl A a)
  | NeId {n} : whne n -> isId n.

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


Lemma isNat_ne t (n : isNat t) : whne t -> ∑ w, n = NeNat w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
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

Lemma isBool_ne t (n : isBool t) : whne t -> ∑ w, n = NeBool w.
Proof.
  intros w.
  depelim n.
  1-2: now inversion w.
  now eexists.
Qed.

Derive Signature for isId.

Lemma isId_refl A a (n : isId (tRefl A a)) : n = ReflId.
Proof.
  depelim n.
  1: reflexivity.
  inversion w ; cbn ; easy.
Qed.

Lemma isId_ne t (n : isId t) : whne t -> ∑ w, n = NeId w.
Proof.
  intros w.
  dependent inversion n ; subst.
  1: inversion w.
  now eexists.
Qed.

(** * Unicity of witnesses *)

Lemma whne_nSucc {t t' k k'} : whne t -> whne t' -> nSucc k t = nSucc k' t' -> t = t' /\ k = k'.
Proof.
  intros net net' [[<- <-]| [(n'&->&<-)|(n&<-&->)]]%nSucc_eq_inv.
  + easy.
  + inversion net.
  + inversion net'.
Qed.

Instance optionEqDec A : EqDec A -> EqDec (option A).
Proof.
  intros eqA ??.
  destruct x as [x|], y as [y|].
  + destruct (eqA x y) as [<-|ne].
    - now left.
    - right. intros e. apply ne.
      now inversion e.
  + right; intros e; inversion e.
  + right; intros e; inversion e.
  + left; constructor.
Qed.


Definition whne_uniq {t} (w1 w2 : whne t) : w1 = w2.
Proof.
  induction w1.
  all: try depelim w2; eauto.
  all: try solve [f_equal; eauto | inversion w1 | inversion w2].
  + destruct (nat_to_term_inj e) as [].
    assert (e = eq_refl) as -> by
      eapply uip.
    cbn in H. eauto.
  + destruct (nSucc_nat_to_term _ _ _ e) as [[] <-]; inversion w2.
  + destruct (whne_nSucc w1 w2 e) as [<- <-].
    assert (e = eq_refl) as ->
      by eapply uip.
    cbn in H; symmetry in H; destruct H.
    f_equal; eauto.
  + destruct (nSucc_nat_to_term _ _ _ (eq_sym e)) as [[] <-]; inversion w1.
  + destruct (whne_nSucc w1 w2 e) as [<- <-].
    assert (e = eq_refl) as ->
      by (unshelve eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    f_equal; eauto.
  + destruct (whne_nSucc w1 w2 e1) as [<- <-].
    assert (e1 = eq_refl) as ->
      by (unshelve eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    assert (Some (kv, S v) = Some (kv0, S v0)) by now rewrite <- e.
    inversion H; subst; clear H.
    f_equal; eauto. eapply uip.
  + destruct (whne_nSucc w1 w2 e') as [<- <-].
    assert (e' = eq_refl) as ->
      by eapply uip.
    cbn in H; symmetry in H; destruct H.
    assert (Some (kv, S v) = Some (kv0, S v0)) by now rewrite <- e.
    inversion H; subst; clear H.
    f_equal; eauto. eapply uip.
Qed.

Derive Signature for isType.

Definition isType_uniq {A} (w1 w2 : isType A) : w1 = w2.
Proof.
  destruct w1; depelim w2; try reflexivity; try solve [inv_whne].
  f_equal; now eapply whne_uniq.
Qed.

Lemma isNat_uniq {t} (p q : isNat t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  f_equal; eapply whne_uniq.
Qed.

Lemma isBool_uniq {t} (p q : isBool t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  f_equal; eapply whne_uniq.
Qed.

Lemma isId_uniq {t} (p q : isId t) : p = q.
Proof.
  destruct p; depind q; try easy; try now inversion w.
  f_equal; eapply whne_uniq.
Qed. 


(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tAlpha {i} : isCanonical (tAlpha i)
  | can_tEval {ℓ v} : isCanonical (tEval ℓ (tRel v))
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

Lemma can_whne_exclusive t : isCanonical t -> whne t -> False.
Proof.
  intros Hcan Hne.
  inversion Hcan ; subst ; inversion Hne.
Qed.

Lemma whnf_can_whne t : whnf t <~> isCanonical t + whne t.
Proof.
  split.
  - intros [].
    all: try solve [left; now constructor | now right].
  - intros [[]|[]]; try now repeat econstructor.
Qed.

Lemma not_can_whne t : whnf t -> ¬ isCanonical t -> whne t.
Proof.
  intros []%whnf_can_whne; eauto.
  now intros [].
Qed.

Lemma not_whne_can t : whnf t -> ¬ whne t -> isCanonical t.
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


  Lemma ren_nSucc_inv {ρ ρε k t t'} : nSucc k t = t'⟨ρ; ρε⟩ -> {u | t = u⟨ρ; ρε⟩ /\ t' = nSucc k u}.
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
  | eq : _ = ?t⟨_; _⟩ |- _ =>
      destruct t ; cbn in * ; try solve [congruence] ;
      inversion eq ; subst ; clear eq;
      change (ren_alpha ?ρε ?t)⟨?ρ⟩ with t⟨ρ; ρε⟩ in *
  end.

  Definition ren_op ρ (o : option (nat × nat)) : option (nat × nat) :=
    match o with
    | Some (n, v) => Some (n, ρ v)
    | None => None
    end.

  Fixpoint headAlpha_ren ρ ρε (head_ren : forall t, head t⟨ρ; ρε⟩ = ren_op ρ (head t))
    i t {struct t} :
    term_under_nSucc (headAlpha head) i t⟨ρ; ρε⟩ = ren_op ρ (term_under_nSucc (headAlpha head) i t) :=
      match t as t'
      return head t'⟨ρ;ρε⟩ = ren_op ρ (head t') ->
        term_under_nSucc _ i t'⟨ρ;ρε⟩ = ren_op ρ (term_under_nSucc _ i t') with
      | tSucc t => fun _ => headAlpha_ren ρ ρε head_ren (S i) t : term_under_nSucc _ (S i) t⟨ρ;ρε⟩ = ren_op ρ (term_under_nSucc _ (S i) t)
      | _ => fun e => e
      end (head_ren t).
  Fixpoint headEval_ren ρ ρε (head_ren : forall t, head t⟨ρ; ρε⟩ = ren_op ρ (head t))
    v i t {struct t}:
    term_under_nSucc (headEval (ρ v) head) i (ren_term ρ (Ren1_Alpha ρε t)) =
    ren_op ρ (term_under_nSucc (headEval v head) i t) :=
      match t as t'
      return head t'⟨ρ;ρε⟩ = ren_op ρ (head t') ->
        term_under_nSucc (headEval (ρ v) head) i (ren_term ρ (Ren1_Alpha ρε t')) =
        ren_op ρ (term_under_nSucc (headEval v head) i t') with
      | tSucc t => fun _ => headEval_ren ρ ρε head_ren v (S i) t
      | tZero => fun _ => eq_refl
      | _ => fun e => e
      end (head_ren t).
  Lemma headXi_aux_ren ρ o : headXi_aux (ren_op (upRen_term_term ρ) o) = ren_op ρ (headXi_aux o).
  Proof. destruct o as [[n []]|]; reflexivity. Qed.
  Fixpoint headXi_ren ρ ρε (head_ren : forall t, head t⟨upRen_term_term ρ; ρε⟩ = ren_op (upRen_term_term ρ) (head t)) i t {struct t}:
    term_under_nSucc (headXi head) i t⟨upRen_term_term ρ;ρε⟩ = ren_op ρ (term_under_nSucc (headXi head) i t) :=
    match t as t'
      return head t'⟨upRen_term_term ρ;ρε⟩ = ren_op (upRen_term_term ρ) (head t') ->
        term_under_nSucc (headXi head) i t'⟨upRen_term_term ρ;ρε⟩ =
        ren_op ρ (term_under_nSucc (headXi head) i t') with
      | tSucc t => fun _ => headXi_ren ρ ρε head_ren (S i) t
      | tApp (tEval _ (tRel _)) t
      | tApp (tAlpha _) t
      | tXi _ t | tXXi _ t _
      | tNatElim _ _ _ t | tBoolElim _ _ _ t | tEmptyElim _ t | tTreeElim _ _ _ t
      | tIdElim _ _ _ _ _ t | tEllElim _ _ _ _ _ _ t
      | tFst t | tSnd t => fun e => eq_trans (f_equal headXi_aux e) (headXi_aux_ren _ _)
      | _ => fun e => e
      end (head_ren t).

  Fixpoint head_ren ρ ρε t {struct t} : head t⟨ρ; ρε⟩ = ren_op ρ (head t).
  Proof. refine
  match t as t' return head t'⟨ρ; ρε⟩ = ren_op ρ (head t') with
  | tApp (tEval _ (tRel v)) t => headEval_ren ρ ρε (head_ren ρ ρε) v 0 t
  | tApp (tAlpha _) t => headAlpha_ren ρ ρε (head_ren ρ ρε) 0 t
  | tXi _ t
  | tXXi _ t _ => headXi_ren ρ ρε (head_ren (upRen_term_term ρ) ρε) 0 t
  | tNatElim _ _ _ t
  | tBoolElim _ _ _ t 
  | tEmptyElim _ t
  | tTreeElim _ _ _ t
  | tFst t | tSnd t
  | tIdElim _ _ _ _ _ t
  | tEllElim _ _ _ _ _ _ t => head_ren _ _ t : head (ren_term ρ (Ren1_Alpha ρε t)) = ren_op ρ (head t)
  | _ => eq_refl
  end.
  Qed.

  Lemma nSucc_ren_inv {ρ ρε t u n} : nSucc n t = u⟨ρ; ρε⟩ -> ∑ t', t = t'⟨ρ; ρε⟩ /\ u = nSucc n t'.
  Proof.
    intros e.
    induction n in u, e |-*.
    + now exists u.
    + destruct u; inversion e as [e']; clear e.
      specialize (IHn _ e') as (t'&->&->).
      now exists t'.
  Qed.

  Variable (ρ ρε: nat -> nat).

  Lemma whne_ren' t : whne t -> whne t⟨ρ; ρε⟩. (* whne nevar⟨ρ⟩ t⟨ρ⟩ <~> whne nevar t. *)
  Proof.
  induction 1 in ρ |-*; cbn.
  2: unfold nat_to_term.
  all : rewrite ? nSucc_ren_alpha, ? nSucc_ren.
  all: try now econstructor.
  + econstructor. 
    { specialize (IHwhne (upRen_term_term ρ)); tea. }
    change (ren1 ?ρ (ren_alpha ?ρε ?n)) with n⟨ρ; ρε⟩.
    now rewrite head_ren, e.
  + econstructor.
    { specialize (IHwhne (upRen_term_term ρ)); tea. }
    change (ren1 ?ρ (ren_alpha ?ρε ?n)) with n⟨ρ; ρε⟩.
    now rewrite head_ren, e.
  Qed.


  Lemma whne_ren t : whne t⟨ρ; ρε⟩ <~> whne t.
  Proof.
    split.
    - remember t⟨ρ; ρε⟩ as t'.
      induction 1 in ρ, ρε, t, Heqt' |-*.
      all: try solve [push_renaming; econstructor; eauto].
      + push_renaming.
        eapply nSucc_ren_inv in H1 as (t2'&e&->).
        do 3 push_renaming.
        now constructor.
      + push_renaming.
        eapply nSucc_ren_inv in H2 as (t2'&->&->).
        push_renaming.
        now constructor.
      + push_renaming.
        eapply nSucc_ren_inv in H2 as (t2'&->&->).
        do 2 push_renaming.
        now constructor.
      + push_renaming.
        eapply nSucc_ren_inv in H2 as (t'&->&->).
        rewrite head_ren in e.
        destruct (head t') as [[? []]|] eqn:eqhead.
        1,3: inversion e.
        econstructor; eauto.
      + push_renaming.
        eapply nSucc_ren_inv in H2 as (t1'&->&->).
        rewrite head_ren in e.
        destruct (head t1') as [[? []]|] eqn:eqhead.
        1,3: inversion e.
        econstructor; eauto.
    - eapply whne_ren'.
  Qed.

  Lemma whnf_ren t : whnf t⟨ρ; ρε⟩ <~> whnf t. 
  Proof.
    split.
    - remember t⟨ρ; ρε⟩ as t'.
      intros Hnf.
      induction Hnf in t, Heqt' |- * ; cbn.
      1-19: try solve [push_renaming ; econstructor ; eauto].
      + do 2 push_renaming; econstructor; eauto.
      + econstructor. subst. eapply whne_ren; eauto.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isType_ren A : isType (A⟨ρ; ρε⟩) <~> isType A.
  Proof.
    split.
    - remember A⟨ρ; ρε⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A :  isPosType (A⟨ρ; ρε⟩) <~> isPosType A.
  Proof.
    split.
    - remember A⟨ρ; ρε⟩ as A'.
      intros Hty.
      induction Hty in A, HeqA' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isFun_ren f :  isFun (f⟨ρ; ρε⟩) <~> isFun f.
  Proof.
    split.
    - remember f⟨ρ; ρε⟩ as f'.
      intros Hfun.
      induction Hfun in f, Heqf' |- * ; cbn.
      1-2: push_renaming ; econstructor ; eauto.
      1 : do 2 push_renaming; econstructor; eauto.
      econstructor. eapply whne_ren. now destruct Heqf'.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.


  Lemma isPair_ren p :  isPair (p⟨ρ; ρε⟩) <~> isPair p.
  Proof.
    split.
    - remember p⟨ρ; ρε⟩ as p'.
      intros Hpair.
      induction Hpair in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isId_ren p : isId (p⟨ρ; ρε⟩) <~> isId p.
  Proof.
    split.
    - remember p⟨ρ; ρε⟩ as p'.
      intros Hid.
      induction Hid in p, Heqp' |- * ; cbn.
      all: push_renaming ; econstructor ; eauto.
      all: now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isCanonical_ren t : isCanonical (t⟨ρ; ρε⟩) <~> isCanonical t.
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: try econstructor.
    change (ren_alpha ?ρε ?t)⟨?ρ⟩ with t⟨ρ; ρε⟩ in *.
    push_renaming. econstructor.
  Qed.

End RenWhnf.

#[global] Hint Constructors isCanonical : gen_typing.
#[global] Hint Constructors whne whnf : gen_typing.
#[global] Hint Resolve neSort nePi neLambda : gen_typing.
#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isTree_whnf isPair_whnf isId_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isBool isTree isId : gen_typing.
#[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren isId_ren isCanonical_ren : gen_typing.
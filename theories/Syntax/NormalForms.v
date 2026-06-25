(** * LogRel.Syntax.NormalForms: definition of normal and neutral forms, and properties. *)
From Stdlib Require Import ssrbool Logic.StrictProp.
From Equations Require Import Equations. (* for depelim *)
From LogRel Require Import AutoSubst.Extra Utils.
From LogRel.Syntax Require Import BasicAst Context Computations.

(** ** Weak-head normal forms and neutrals. *)
Section NormalForms.
  Context {red : term -> term -> Type}.

Inductive whns {k v : nat} : term -> Type :=
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
  | whns_tXXiRed ℓ m n n' k' km : @whns k' 0 m -> notin_ell (ℓ : ell) k' ->
    red (tApp (tEval ℓ n) (nat_to_term k')) n' -> whns n' ->
    whns (tXXi ℓ (nSucc km m) n).
Arguments whns : clear implicits.

Inductive whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tBoolElim {P ht hf n} : whne n -> whne (tBoolElim P ht hf n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tTreeElim {P hl hn n} : whne n -> whne (tTreeElim P hl hn n)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
  | whne_tIdElim {A x P hr y e} : whne e -> whne (tIdElim A x P hr y e)
  | whne_tAlpha {i t k} : whne t -> whne (tApp (tAlpha i) (nSucc k t))
  | whne_tXi {n ℓ k} : whne n -> whne (tXi ℓ (nSucc k n))
  | whne_tXXi {m n ℓ k} : whne m -> whne (tXXi ℓ (nSucc k m) n)
  | whne_tXXiRed {ℓ m n n' k km} : whns k 0 m -> notin_ell (ℓ : ell) k ->
      red (tApp (tEval ℓ n) (nat_to_term k)) n' -> whne n' ->
      whne (tXXi ℓ (nSucc km m) n).

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
  | whnf_whne {n} : whne n -> whnf n
  | whnf_whns {n v k} : @whns k v n -> whnf n.

(* #[global] Hint Constructors whne whnf : gen_typing. *)

Equations Derive Signature for whns.
Equations Derive Signature for whne.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

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
  | NeFun  {f} : whne f -> isFun f.

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
Proof. destruct i; now constructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now constructor. Defined.

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

(* #[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isTree_whnf isPair_whnf isId_whnf : gen_typing. *)
(* #[global] Hint Constructors isPosType isType isFun isNat isBool isTree isId : gen_typing. *)

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

  #[local] Ltac nSucc_handler :=
  try match goal with
  | eq : nSucc ?k ?t = nSucc ?k' ?t' |- _ =>
      eapply nSucc_eq_inv in eq as [[<- <-] | [(?&->&<-)|(?&<-&->)]]
  end.

Definition whns_uniq_kv {t} {k1 v1 k2 v2} (w1 : whns k1 v1 t) (w2 : whns k2 v2 t) : k1 = k2 /\ v1 = v2.
Proof.
  induction w1 in k2, v2, w2 |-*. all: depelim w2; nSucc_handler.
  all: try solve [inversion w1 | inversion w2].
  all: try (specialize (IHw1 _ _ ltac:(tea)) as (<-&ev);
    now inversion ev).
  + eapply nat_to_term_inj in H as <-.
    repeat constructor.
  + inversion w2_1.
  + specialize (IHw1_1 _ _ w2)as (<-&ev).
    inversion ev.
  + inversion w1_1.
  + specialize (IHw1_1 _ _ w2_1) as [-> _]; clear w2_1.
    assert (n' = n'0) as <- by admit.
    now specialize (IHw1_2 _ _ w2_2). 
  + inversion w1_1.
  + inversion w2_1.
Admitted.

Definition whns_uniq {t} k1 v1 k2 v2 (w1 : whns k1 v1 t) (w2 : whns k2 v2 t) :
  exists (ek : k1 = k2) (ev : v1 = v2), eq_rect _ (fun v => whns k2 v t) (eq_rect _ (fun k => whns k v1 t) w1 _ ek) _ ev = w2.
Proof.
  induction w1 in v2, w2 |-*. all: depelim w2.
  all: try solve [inversion w1 | inversion w2].
  all: try (specialize (IHw1 v2 w2) as (<-&<-&<-);
    solve [repeat unshelve econstructor]).
  + pose proof (nat_to_term_inj e) as <-.
    assert (e = eq_refl) as -> by
      (enough (uip : UIP term) by eapply uip; typeclasses eauto).
    cbn in H; symmetry in H; destruct H.
    repeat unshelve econstructor.
  + pose proof (nSucc_eq_inv e) as [[<- <-] | [(?&->&<-)|(?&<-&->)]].
    - assert (e = eq_refl) as -> by
        (enough (uip : UIP term) by eapply uip; typeclasses eauto).
      cbn in H; symmetry in H; destruct H.
      specialize (IHw1 v2 w2) as (<-&<-&<-).
      repeat unshelve econstructor.
    - inversion w1.
    - inversion w2.
  + pose proof (nSucc_eq_inv e) as [[<- <-] | [(?&->&<-)|(?&<-&->)]].
    - assert (e = eq_refl) as -> by
        (enough (uip : UIP term) by eapply uip; typeclasses eauto).
      cbn in H; symmetry in H; destruct H.
      specialize (IHw1 _ w2) as (<-&ev&ew).
      inversion ev; subst.
      assert (ev = eq_refl) as -> by
        (enough (uip : UIP _) by eapply uip; typeclasses eauto).
      repeat unshelve econstructor.
    - 
      speci
    inversion w0; subst.
    { inversion X. }
    specialize (IHw1 w2) as (<-&<-&<-).
  + specialize (IHw1 w2) as (<-&<-&<-).
    repeat unshelve econstructor.
  + specialize (IHw1 w2) as (<-&<-&<-).
    repeat unshelve econstructor.
  + 

Lemma whne_whns_false {t k v} : whne t -> whns k v t -> False.
Proof.
  intros net nst.
  induction net in k, v, nst |-*.
  1-13 : depelim nst; nSucc_handler; eauto.
  all: try solve [inversion net|inversion nst].
  + inversion nst1.
  + admit.
  + inversion w.
  + admit.
  + inversion w.
  + inversion nst1.
  inversion nst; subst.
    assert (k = k0) as -> by admit.
    assert (v = 0) as -> by admit.
    
    depelim nst.
    specialize (hred _ _ _ _ n0 r) as ->.
    inversion net; subst.
    inversion X.
Qed.



Definition whne_uniq {t} (hred : red_notin) (w1 w2 : whne t) : w1 = w2.
Proof.
  induction w1. all: depelim w2; f_equal; eauto.
  1-2: solve [depelim w1 | now depelim w2].
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
  + eapply nSucc_eq_inv in e' as e''.
    destruct e'' as [[<- <-] | [(?&->&<-)|(?&<-&->)]].
    - assert (e' = eq_refl) as -> by
        (enough (uip : UIP term) by eapply uip; typeclasses eauto).
      cbn in H; symmetry in H; destruct H.
      destruct (whne_whns_false hred w1 w).
    - inversion w1.
    - inversion w.
  + eapply nSucc_eq_inv in e' as e''.
    destruct e'' as [[<- <-] | [(?&->&<-)|(?&<-&->)]].
    - assert (e' = eq_refl) as -> by
        (enough (uip : UIP term) by eapply uip; typeclasses eauto).
      cbn in H; symmetry in H; destruct H.
      destruct (whne_whns_false hred w2 w).
    - inversion w.
    - inversion w2.
  + eapply nSucc_eq_inv in e' as e''.
    destruct e'' as [[<- <-] | [(?&->&<-)|(?&<-&->)]].
    - assert (e' = eq_refl) as -> by
        (enough (uip : UIP term) by eapply uip; typeclasses eauto).
      cbn in H; symmetry in H; destruct H.
      specialize (hred _ _ _ _ n0 r) as ->.
      inversion w1. inversion X.
    - inversion w.
    - inversion w2.
Qed.

Derive Signature for isType.

(* Definition isType_uniq {A} (w1 w2 : isType A) : w1 = w2.
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
Qed.  *)


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

(* #[global] Hint Constructors isCanonical : gen_typing. *)

Lemma can_whne_exclusive t : isCanonical t -> whne t -> False.
Proof.
  intros Hcan Hne.
  inversion Hcan ; subst ; inversion Hne.
Qed.
(* 
Lemma whnf_can_whne t : whnf t <~> isCanonical t + whne t + { k & {v & whns k v t}}.
Proof.
  split.
  - intros [].
    all: try solve [left; now constructor | now right].
  - intros [[]|[]]; try now do 2 constructor.
Qed.

(* Lemma not_can_whne t : whnf t -> ¬ isCanonical t -> whne t.
Proof.
  intros [[]|]%whnf_can_whne ; eauto.
  now intros [].
Qed.

Lemma not_whne_can t : whnf t -> ¬ whne t -> isCanonical t.
Proof.
  intros []%whnf_can_whne ; eauto.
  now intros [].
Qed.
 *)
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
 *)
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
(* 
  Variable (ρ (* ρε *): nat -> nat).

  Lemma whne_ren t : whne t -> whne t⟨ρ⟩. (* whne (t⟨ρ(* ; ρε *)⟩) <~> whne t. *)
  Proof.
(*     split.
    - remember t⟨ρ(* ; ρε *)⟩ as t'.
      intros Hne.
      induction Hne in ρ, t, Heqt' |- * ; cbn.
      1-9: try (repeat push_renaming; econstructor ; now eauto).
      + push_renaming.
        eapply ren_nSucc_inv in H1.
        destruct H1 as [u [-> ->]].
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
    - induction 1 in ρ |-*; cbn.
      10-13 : rewrite nSucc_ren.
      all: try now econstructor.
      eapply whne_tXXiRed, IHX; tea.
  Qed. *)

(*   Lemma whnf_ren t : whnf (t⟨ρ⟩) <~> whnf t.
  Proof.
    split.
    - remember t⟨ρ⟩ as t'.
      intros Hnf.
      induction Hnf in t, Heqt' |- * ; cbn.
      1-19: push_renaming ; econstructor ; eauto.
      1-13: try now eapply whne_ren ; cbn.
    - induction 1 ; cbn.
      all: econstructor.
      now eapply whne_ren.
  Qed.

  Lemma isType_ren A : isType (A⟨ρ⟩) <~> isType A.
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
  Qed.

  Lemma isCanonical_ren t : isCanonical (t⟨ρ⟩) <~> isCanonical t.
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: now econstructor.
  Qed. *)

End RenWhnf.
End NormalForms.
Arguments whns {_} _ _.

#[global] Hint Constructors isCanonical : gen_typing.
#[global] Hint Constructors whne whnf : gen_typing.
#[global] Hint Resolve neSort nePi neLambda : gen_typing.
#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isBool_whnf isTree_whnf isPair_whnf isId_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat isBool isTree isId : gen_typing.
(* #[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren isId_ren isCanonical_ren : gen_typing. *)
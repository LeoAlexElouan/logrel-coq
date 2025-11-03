(** * LogRel.Syntax.Context: definition of contexts and operations on them.*)
From Stdlib Require Import ssreflect Morphisms Setoid.
From LogRel Require Import Utils BasicAst AutoSubst.Extra.
From Equations Require Import Equations.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Definition Tcontext := list term.


Definition preFcontext := list (nat × bool).

Inductive not_in_Fctx : preFcontext -> nat -> SProp :=
  | not_in_nil n : not_in_Fctx nil n
  | not_in_nowhere (L : preFcontext) n n' b' : (n <> n') -> not_in_Fctx L n -> (not_in_Fctx (cons (n',b') L) n).

Inductive wfFcontext : preFcontext -> SProp :=
  | wf_nil : wfFcontext nil
  | wf_cons {n b L} : wfFcontext L -> not_in_Fctx L n -> wfFcontext (cons (n,b) L).

Record Fcontext :={
  preFctx :> preFcontext;
  wfF : wfFcontext preFctx;
  }.

Definition Fcons' (L:Fcontext) {n} (ne : not_in_Fctx L n) b : Fcontext
  := Build_Fcontext (cons (n,b) (preFctx L)) (wf_cons (wfF L) ne).

Definition Fnil := Build_Fcontext nil wf_nil.


Record context := {
  Tctx :> Tcontext;
  Fctx :> Fcontext;
  }.

Definition nilctx := Build_context nil Fnil.
Definition Tcons Γ d := Build_context (cons d (Tctx Γ)) (Fctx Γ).

Record newnat L := {
  newnat_nat :> nat;
  newnat_new :> not_in_Fctx L newnat_nat;
  }.


Definition Fcons Γ (new : newnat (Fctx Γ)) b := Build_context (Tctx Γ) (Fcons' (Fctx Γ) new b).
Definition appctx Δ Γ := Build_context (app Δ (Tctx Γ)) (Fctx Γ).
Definition fromTctx Γ := Build_context Γ Fnil.
Definition fromFctx L := Build_context nil L.


Notation "'ε'" := nilctx.
Notation " Γ ,, d " := (Tcons Γ d) (at level 20, d at next level).
Notation " Γ ,, new ↦ b " := (Fcons Γ new b) (at level 20, new at next level, b at next level).
Notation " Γ ,,, Δ " := (appctx Δ Γ) (at level 25, Δ at next level, left associativity).

(** States that a definition, correctly weakened, is in a context. *)
Inductive in_Tctx : Tcontext -> nat -> term -> Type :=
  | in_here (Γ : Tcontext) d : in_Tctx (cons d Γ) 0 (d⟨↑⟩)
  | in_there (Γ : Tcontext) d d' n : in_Tctx Γ n d -> in_Tctx (cons d' Γ) (S n) (ren_term shift d).

Definition in_ctx Γ := in_Tctx (Tctx Γ).

Inductive in_Fctx : preFcontext -> nat -> bool -> SProp :=
  | in_hereF (L : preFcontext) n b : in_Fctx (cons (n,b) L)  n b
  | in_thereF (L : preFcontext) n b n' b' : in_Fctx L n b -> in_Fctx (cons (n', b') L)n b.



Lemma in_Tctx_inj Γ n decl decl' :
  in_Tctx Γ n decl -> in_Tctx Γ n decl' -> decl = decl'.
Proof.
  induction 1 in decl' |- *; inversion 1 ; subst.
  1: reflexivity.
  now f_equal.
Qed.

Lemma Tctx_induction P : (forall L, P (fromFctx L)) -> (forall Γ A, P Γ -> P (Γ,,A)) -> forall Γ, P Γ.
Proof.
  intros hL hcons [Γ L].
  induction Γ.
  - apply hL.
  - now apply (hcons (Build_context Γ L) a).
Qed.

(* Properties of in_Fctx *)

Inductive SFalse : SProp := .
Inductive STrue : SProp := SI.
(* Inductive SAnd (A B : SProp) : SProp := Sconj (a : A) (b : B). *)
(* Inductive or_tricho {P Q R : SProp} : Type :=
  | in_left (p :P)
  | in_mid (q : Q)
  | in_right (r : R). 

Inductive SSig {A : Type} (P : A -> SProp): SProp :=
  | SExist : forall Sproj1 : A, P Sproj1 -> SSig P.
Inductive SOr (A B : SProp) : SProp :=
  | SOr_introl : A -> SOr A B
  | SOr_intror : B -> SOr A B.

Arguments SOr_introl {_ _}.
Arguments SOr_intror {_ _}.
Arguments or_tricho : clear implicits. *)

Inductive decide_in_type L n : Type :=
  | is_in b : (in_Fctx L n b) -> decide_in_type L n
  | is_notin : not_in_Fctx L n -> decide_in_type L n.

Arguments is_in {_ _}.
Arguments is_notin {_ _}.

Lemma decide_in L n : decide_in_type L n.
Proof.
  induction L as [|[n' b'] L [b hin|hnotin]].
  - right.
    constructor.
  - apply (is_in b).
    now apply in_thereF.
  - pose proof (PeanoNat.Nat.eq_dec n n') as e.
    destruct e as [<-|].
    + apply (is_in b').
      constructor.
    + right.
      now eapply not_in_nowhere.
Qed.
(* Lemma trichotomy L n : or_tricho (in_Fctx L n true) (in_Fctx L n false) (not_in_Fctx L n).
Proof.
  induction L.
  - apply in_right.
    constructor.
  - destruct a as [n' b'].
    destruct IHL.
    + apply in_left.
      now apply in_thereF.
    + apply in_mid.
      now apply in_thereF.
    + pose proof (PeanoNat.Nat.eq_dec n n') as e.
      destruct e as [<-|].
      1: destruct b'.
      * apply in_left.
        constructor.
      * apply in_mid.
        constructor.
      * apply in_right.
        now eapply not_in_nowhere.
Defined. *)

Lemma notin_is_not_in {L n b} : not_in_Fctx L n -> in_Fctx L n b -> SFalse.
Proof.
  intros hnotin hin.
  induction hin.
  - inversion hnotin ; subst.
    easy.
  - eapply IHhin.
    now inversion hnotin ; subst.
Qed.

Lemma functionality (L:Fcontext) n b b': in_Fctx L n b -> in_Fctx L n b' -> b = b'.
Proof.
  intros hin hin'.
  destruct L as [L wfL].
  destruct b, b'; auto.
  all: enough (H : SFalse) by inversion H; revert hin hin'.
  + induction wfL; intros hin hin'; inversion hin; subst; inversion hin'; subst.
    - now eapply notin_is_not_in.
    - now eapply notin_is_not_in.
    - easy.
  + induction wfL; intros hin hin'; inversion hin; subst; inversion hin'; subst.
    - now eapply notin_is_not_in.
    - now eapply notin_is_not_in.
    - easy.
Qed.

Lemma functionality_inversion (L : Fcontext) n : in_Fctx L n true -> in_Fctx L n false -> SFalse.
Proof.
  intros hinf hint.
  pose proof (functionality _ _ _ _ hinf hint) as eqtf.
  inversion eqtf.
Qed.

Lemma decide_in_in (L : Fcontext) n b (hin : in_Fctx L n b) :
  decide_in L n = is_in b hin.
Proof.
  destruct (decide_in L n) as [b' hin'|hnotin].
  - destruct (functionality L n b b' hin hin').
    reflexivity.
  - destruct (notin_is_not_in hnotin hin).
Qed.
(* 
Lemma trichotomy_in (L : Fcontext) n b (hin : in_Fctx L n b) :
  trichotomy L n = match b return (forall (hin : in_Fctx L n b), _) with true => fun hin => in_left hin| false => fun hin => in_mid hin end hin.
Proof.
  destruct (trichotomy L n).
  1,2: destruct b.
  1,4: reflexivity.
  + destruct (functionality_inversion L n p hin).
  + destruct (functionality_inversion L n hin q).
  + destruct (notin_is_not_in r hin).
Qed. *)
(* equality of new nat*)

Lemma new_eq_is_nat_eq {Γ} (new new' : newnat Γ) :
  newnat_nat _ new = newnat_nat _ new' -> new = new'.
Proof.
  destruct new as [n new],new' as [n' new']. cbn.
  intros <-. reflexivity.
Qed.

Lemma new_eq_dec {Γ} (new new' : newnat Γ) : {new  = new'} + {new <> new'}.
Proof.
  destruct (PeanoNat.Nat.eq_dec new new').
  - left. now apply new_eq_is_nat_eq.
  - right. intros e. apply n. now apply (f_equal (newnat_nat _)).
Qed.

(* Equality decidability *)

Lemma f_equal2 :
forall {A1 A2 B:Type} (f:A1 -> A2 -> B) {x1 y1:A1}
  {x2 y2:A2}, x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof. now intros * <- <-. Defined.

Definition Build_context_eq {Γ Γ' L L'} (eΓ : Γ = Γ') (eL : L = L'):
  Build_context Γ L = Build_context Γ' L':=
  f_equal2 Build_context eΓ eL.

Lemma Build_context_eq_inv {Γ Γ'} (e : Γ = Γ') : e = Build_context_eq (f_equal Tctx e) (f_equal Fctx e).
Proof. destruct e; reflexivity. Qed.

Definition Build_Fcontext_eq {L L' wfL wfL'} (eL : L = L'):
  Build_Fcontext L wfL= Build_Fcontext L' wfL'.
Proof. destruct eL; reflexivity. Defined.

Definition Build_Fcontext_eq_inv {L L'} (eL : L = L'):
  eL = Build_Fcontext_eq (f_equal preFctx eL).
Proof. destruct eL; reflexivity. Qed.


Instance FctxEqDec : EqDec Fcontext.
Proof.
  intros [L wfL] [L' wfL'].
  destruct (eq_dec L L') as [<-|ne].
  - left. reflexivity.
  - right. intros e. apply ne. apply (f_equal preFctx e).
Qed.


Instance ctxqDec : EqDec context.
Proof.
  intros [Γ L] [Γ' L'].
  destruct (eq_dec Γ Γ') as [<-|neΓ].
  destruct (eq_dec L L') as [<-|neL].
  + left; reflexivity.
  + right. intros e. apply neL. apply (f_equal Fctx e).
  + right. intros e. apply neΓ. apply (f_equal Tctx e).
Qed.

(* Inversions *)

Lemma wfFcons_notin {L n b} : wfFcontext (cons (n,b) L) -> not_in_Fctx L n.
Proof.
  intros wf.
  change (match ((n, b)::L)%list  with nil => STrue | cons (pair n b) L => not_in_Fctx L n end).
  induction wf; easy.
Qed.

Definition wfFcons_new {L n b} : wfFcontext (cons (n,b) L) -> newnat L :=
  fun wfL => Build_newnat L n (wfFcons_notin wfL).

Lemma wfFcons_wfF {L n b} : wfFcontext (cons (n,b) L) -> wfFcontext L.
Proof.
  intros wf.
  change (match ((n, b)::L)%list  with nil => STrue | cons (pair n b) L => wfFcontext L end).
  induction wf; easy.
Qed.


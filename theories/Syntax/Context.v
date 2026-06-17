(** * LogRel.Syntax.Context: definition of contexts and operations on them.*)
From Stdlib Require Import ssreflect Morphisms Setoid Logic.StrictProp Lia.
From LogRel Require Import Utils BasicAst AutoSubst.Extra.
From Equations Require Import Equations.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)

Fixpoint in_ell (ℓ : ell_list) n b : Prop :=
  match ℓ with
  | nil => False
  | cons (Datatypes.pair n' b') ℓ => ((n = n') /\ (b = b')) \/ (in_ell ℓ n b)
  end.

Fixpoint notin_ell (ℓ : ell_list) n : Prop :=
  match ℓ with
  | nil => True
  | cons (Datatypes.pair n' _) ℓ => (n <> n') /\ (notin_ell ℓ n)
  end.


Record newnat ℓ := {
  newnat_nat :> nat;
  newnat_new :> Squash (notin_ell ℓ newnat_nat);
  }.


Fixpoint cons_ell_list (ℓ : ell_list) (n : nat) (b : bool) : ell_list :=
  match ℓ as ℓ with
  | nil => cons (Datatypes.pair n b) nil
  | cons (Datatypes.pair n' b') ℓ' => match Compare_dec.lt_dec n n' with
    | left _ => cons (Datatypes.pair n b) ℓ
    | right _ => cons (Datatypes.pair n' b') (cons_ell_list ℓ' n b)
    end
  end.

Lemma lt_lt_ell ℓ n n': n < n' -> lt_ell n' ℓ -> lt_ell n ℓ.
Proof.
  intros ltn ltn'.
  induction ℓ as [| [n'' b''] ℓ ihℓ].
  + constructor.
  + cbn in *.
    constructor.
    - lia.
    - now eapply ihℓ.
Qed.

Lemma lt_cons_ell (ℓ : ell_list) n' b' n : n < n' -> lt_ell n ℓ -> lt_ell n (cons_ell_list ℓ n' b').
Proof.
  intros ltnn' ltn.
  induction ℓ as [|[n'' b''] ℓ ihℓ].
  + simpl. lia.
  + simpl in *.
    destruct (Compare_dec.lt_dec n' n'') as [ltn'n''| nltn'n'']; now simpl.
Qed.

Lemma cons_ell_wf (ℓ : ell) (new : newnat ℓ) (b : bool) : Squash (ell_wf (cons_ell_list ℓ new b)).
Proof.
  destruct ℓ as [ℓ [wf]], new as [n [new]]; constructor; cbn in *.
  induction ℓ as [|[n' b'] ℓ].
  + simpl. easy.
  + simpl.
    destruct (Compare_dec.lt_dec n n') as [ltnn'| nltnn']; simpl in *.
    - repeat constructor; try easy.
      now eapply lt_lt_ell.
    - constructor.
      * eapply lt_cons_ell, wf.
        lia.
      * now eapply IHℓ.
Qed.

Definition cons_ell (ℓ: ell) (new : newnat ℓ) b : ell
  := Build_ell (cons_ell_list ℓ new b) (cons_ell_wf _ _ _).


Notation nil_ell := (Build_ell nil (squash I)).



Inductive list_index' {X : Set} : Set :=
  | index_0 : list_index'
  | index_S (i : X) : list_index'.

Fixpoint list_index {A} (l : list A) : Set :=
  match l with
  | nil => False
  | cons h t => @list_index' (list_index t)
  end.

Fixpoint index_induction {A} (P : forall (l : list A), list_index l -> Type)
  (h0 : forall h t, P (cons h t) index_0)
  (hS : forall h t (i : list_index t), P t i -> P (cons h t) (index_S i))
  (l : list A) {struct l}: forall i : list_index l, P l i :=
  match l as l' return forall i' : list_index l', P l' i' with
  | nil => fun i : False => match i with end 
  | cons h t => fun i =>
    match i with
    | index_0 => h0 _ _
    | index_S i' => hS _ _ i' (index_induction P h0 hS t i')
    end
  end.

Fixpoint Sindex_induction {A} (P : forall (l : list A), list_index l -> SProp)
  (h0 : forall h t, P (cons h t) index_0)
  (hS : forall h t (i : list_index t), P t i -> P (cons h t) (index_S i))
  (l : list A) {struct l}: forall i : list_index l, P l i :=
  match l as l' return forall i' : list_index l', P l' i' with
  | nil => fun i : False => match i with end 
  | cons h t => fun i =>
    match i with
    | index_0 => h0 _ _
    | index_S i' => hS _ _ i' (Sindex_induction P h0 hS t i')
    end
  end.


(* 
Inductive list_index {A} : list A -> Set :=
  | index_0 h t : list_index (cons h t)
  | index_S h t (i : list_index t) : list_index (cons h t). *)
(* Lemma index_case {A : Set} {h: A} {t} P : (P h t (index_0 h t)) -> (forall i, P h t (index_S h t i)) -> forall i, P h t i.
Proof.
  intros h0 hS i.
  revert h0 hS.
  pattern h, t, i.
  change (?A h t i) with (match cons h t as l return list_index l -> Type with nil => fun i => unit | cons h' t' => fun i => A h' t' i end i).
  destruct i; auto.
Defined.
Lemma index_caseS {A : Set} {h: A} {t} (P : forall h t i, SProp) : (P h t (index_0 h t)) -> (forall i, P h t (index_S h t i)) -> forall i, P h t i.
Proof.
  intros h0 hS i.
  revert h0 hS.
  pattern h, t, i.
  change (?A h t i) with (match cons h t as l return list_index l -> SProp with nil => fun i => sUnit | cons h' t' => fun i => A h' t' i end i).
  destruct i; auto.
Qed. *)

Definition index_to_nat {A}  : forall {l : list A}, list_index l -> nat := index_induction _ (fun _ _ => 0) (fun _ _ _ => S).

(* Fixpoint index_to_nat {A} {l : list A} (i : list_index l) (* {struct l} *) := match l as l' return list_index l' -> nat with
  | nil => fun i => match i with end
  | cons h t => fun i => match i with index_0 => 0 | index_S i' => S (index_to_nat i') end
  end i. *)
Lemma index_to_nat_inj {A}  {l : list A} {i i': list_index l} (ei : index_to_nat i = index_to_nat i') : i = i'.
Proof.
  induction l, i using index_induction; destruct i';
  cbn in *; inversion ei.
  - reflexivity.
  - f_equal. auto.
Qed.

Coercion index_to_nat : list_index >-> nat.

Definition list_at {A} : forall (l : list A ) (i : list_index l), A := index_induction (fun _ _ => A) (fun h _ => h) (fun _ _ _ a => a).

Definition Fcons (L : list ell) (i : list_index L) :
  forall (new : newnat (list_at L i)) (b : bool), list ell :=
  index_induction (fun (L : list ell) i => forall (new : newnat (list_at L i)) (b : bool), list ell)
    (fun h t new b => cons (cons_ell h new b) t)
    (fun h t i IH new b => cons h (IH new b)) L i.

Inductive decl :=
  | term_decl (t : term)
  | ell_decl (ℓ : ell).
Coercion term_decl : term >-> decl.
Coercion ell_decl : ell >-> decl.
Equations Derive NoConfusion Subterm EqDec for decl.
Instance ren_decl : Ren1 (nat -> nat) decl decl := fun ρ d =>
  match d with
  | term_decl t => term_decl t⟨ρ⟩
  | ell_decl ℓ => ell_decl ℓ
  end.
#[global]
Instance ren_decl_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_decl)).
Proof.
  intros ρl ρr ρeq [t|ℓ] dr <-; simpl.
  + now rewrite ρeq.
  + reflexivity.
Qed.

Definition Tcontext := list decl.
Record context := {
  Tctx :> Tcontext;
  Fctx :> list ell;
  }.

Notation nilctx := (Build_context nil nil).
(* Definition Tcons Γ d := Build_context (cons d (Tctx Γ)) (Fctx Γ). *)


(* Definition Fcons Γ (new : newnat (Fctx Γ)) b := Build_context (Tctx Γ) (Fcons' (Fctx Γ) new b). *)
Definition appctx Δ Γ := Build_context (app Δ (Tctx Γ)) (Fctx Γ).
Definition fromTctx Γ := Build_context Γ nil.
Definition fromFctx L := Build_context nil L.


Notation "'ε'" := nilctx.
Notation " Γ ,, d " := (Build_context (cons d (Tctx Γ)) (Fctx Γ)) (at level 20, d at next level).
Notation " Γ ,, i : new ↦ b " := (Build_context (Tctx Γ) (Fcons (Fctx Γ) i new b)) (at level 20, new at next level, b at next level).
Notation " Γ ,, ↦ F" := (Build_context (List.map (ren_alpha S) (Tctx Γ)) (cons F (Fctx Γ))).
Notation " Γ ,,, Δ " := (appctx Δ Γ) (at level 25, Δ at next level, left associativity).

Lemma cons_Fcons Γ A i new b : Γ,, i : new ↦ b ,, A = Γ,, A ,, i : new ↦ b. 
Proof. reflexivity. Qed.

(** States that a definition, correctly weakened, is in a context. *)
Inductive in_Tctx : Tcontext -> nat -> decl -> Type :=
  | in_here (Γ : Tcontext) (A : decl) : in_Tctx (cons A Γ) 0 (A⟨↑⟩)
  | in_there (Γ : Tcontext) A A' n : in_Tctx Γ n A -> in_Tctx (cons A' Γ) (S n) (A⟨↑⟩).

Definition in_ctx Γ := in_Tctx (Tctx Γ).

(* Lemma in_ctx_induction : forall P : forall Γ n A, in_ctx Γ n A -> Type,
  (forall Γ A, P (Γ,, A) 0 A⟨↑⟩ (in_here Γ A)) ->
  (forall Γ A A' n (hin : in_ctx Γ n A),
    P Γ n A hin -> P _ (S n) A⟨↑⟩ (in_there Γ A A' n hin)) ->
  forall Γ n A (hin : in_ctx Γ n A), P Γ n A hin.
Proof.
  intros ? hhere hthere *. change Γ with (Build_context Γ Γ). induction hin.
  + specialize (hhere (Build_context Γ0 Γ)).
    eapply hhere.
  + specialize (hthere (Build_context Γ0 Γ)).
    now eapply hthere.
Qed. *)




Lemma in_Tctx_inj Γ n decl decl' :
  in_Tctx Γ n decl -> in_Tctx Γ n decl' -> decl = decl'.
Proof.
  induction 1 in decl' |- *; inversion 1 ; subst.
  1: reflexivity.
  now f_equal.
Qed.

Lemma Tctx_induction P : (forall L, P (fromFctx L)) ->
  (forall Γ A, P Γ -> P (Γ,,A)) -> forall Γ, P Γ.
Proof.
  intros hL hcons [Γ L].
  induction Γ as [| d Γ].
  - apply hL.
  - now apply (hcons (Build_context Γ L) d).
Qed.


(* Properties of in_Fctx *)

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

Definition SIsNil {A} (L : list A) : SProp :=
  match L with
  | nil => STrue
  | cons _ _ => SFalse
  end.

Inductive decide_in_type L n : Type :=
  | is_in b : Squash (in_ell L n b) -> decide_in_type L n
  | is_notin : Squash (notin_ell L n) -> decide_in_type L n.

Arguments is_in {_ _}.
Arguments is_notin {_ _}.

Lemma decide_in L n : decide_in_type L n.
Proof.
  induction L as [|[n' b'] L [b hin|hnotin]].
  - right.
    repeat constructor.
  - apply (is_in b). destruct hin; constructor.
    now simpl.
  - pose proof (PeanoNat.Nat.eq_dec n n') as e.
    destruct e as [<-|].
    + apply (is_in b').
      repeat constructor.
    + right.
      destruct hnotin; constructor.
      now simpl.
Qed.

Lemma notin_is_not_in {L n b} : notin_ell L n -> in_ell L n b -> SFalse.
Proof.
  intros hnotin hin.
  induction L as [|[n' b'] L ihL].
  + destruct hin.
  + simpl in *.
    destruct hin.
    - lia.
    - easy.
Qed.

Lemma not_in_is_notin' {L n} : (in_ell L n true -> SFalse) -> (in_ell L n false -> SFalse) -> notin_ell L n.
Proof.
  intros hnotint hnotinf.
  induction L as [|[n' b'] L ihL].
  + constructor.
  + simpl in *.
    constructor.
    - intros <-.
      assert SFalse as [].
      destruct b'.
      * eapply hnotint; repeat constructor.
      * eapply hnotinf; repeat constructor.
    - easy.
Qed.

Lemma not_in_is_notin {L n} : (forall b, in_ell L n b -> SFalse) -> notin_ell L n.
Proof.
  intros.
  now eapply not_in_is_notin'.
Qed.

Lemma lt_notin ℓ n : lt_ell n ℓ -> notin_ell ℓ n.
Proof.
  induction ℓ as [|[n' b'] ℓ ihℓ]; simpl; constructor.
  + lia.
  + easy.
Qed.

Lemma functionality_inversion (L : ell) n : Squash (in_ell L n true) -> Squash (in_ell L n false) -> SFalse.
Proof.
  intros int inf.
  destruct L as [ L [wfL]].
  induction L as [|[n' b'] L ihL] in wfL, int, inf |-*; simpl in *.
  {destruct int as [[]]. }
  destruct int as [[[-> <-] |int]], inf as [[[en eb]| inf]].
  + inversion eb.
  + eapply notin_is_not_in, inf.
    now eapply lt_notin.
  + destruct en. eapply notin_is_not_in, int.
    now eapply lt_notin.
  + eapply ihL; try easy; constructor; easy.
Qed.

Lemma functionality (L:ell) n b b': Squash (in_ell L n b) -> Squash (in_ell L n b') -> b = b'.
Proof.
  intros hin hin'.
  destruct L as [L wfL].
  destruct b, b'; auto.
  all: enough (H : SFalse) by destruct H;
    now eapply functionality_inversion.
Qed.


Lemma decide_in_in (L : ell) n b (hin : Squash (in_ell L n b)) :
  decide_in L n = is_in b hin.
Proof.
  destruct (decide_in L n) as [b' hin'|hnotin].
  - destruct (functionality L n b b' hin hin').
    reflexivity.
  - enough (H : SFalse) by destruct H.
    destruct hin as [hin], hnotin as [hnotin].
    destruct (notin_is_not_in hnotin hin).
Qed.

Lemma decide_in_new (L : ell) (new : newnat L) :
  decide_in L new = is_notin new.
Proof.
  destruct (decide_in L new) as [b hin|hnotin].
  - enough (H : SFalse) by destruct H.
    destruct hin as [hin].
    destruct new as [n [new]].
    destruct (notin_is_not_in new hin).
  - reflexivity.
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

Definition Build_ell_eq {L L' wfL wfL'} (eL : L = L'):
  Build_ell L wfL= Build_ell L' wfL'.
Proof. destruct eL; reflexivity. Defined.

Definition Build_ell_eq_inv {L L'} (eL : L = L'):
  eL = Build_ell_eq (f_equal ℓ_list eL).
Proof. destruct eL; reflexivity. Qed.

Lemma cons_eq_inversion' {Γ Γ' : Tcontext} {d d': decl} {P} (e : cons d Γ = cons d' Γ') : P Γ d eq_refl -> P Γ' d' e.
Proof.
  intros.
  change ((match cons d' Γ' with cons d0 Γ0 => fun e => P Γ0 d0 e | _ => fun _ => unit:Type end) e).
  now destruct e.
Qed.

Lemma cons_eq_inversion {Γ A Γ' A'} P : P Γ A eq_refl -> forall e : Γ,,A = Γ',,A', P Γ' A' e.
Proof.
  intros hP e.
  rewrite (Build_context_eq_inv e).
  set (eF := f_equal Fctx e); clearbody eF.
  set (eT := f_equal Tctx e); clearbody eT.
  destruct Γ as [Γ L], Γ' as [Γ' L']; cbn in *.
  destruct eF.
  pattern Γ', A', eT.
  now eapply (cons_eq_inversion' eT).
Defined.


Equations Derive NoConfusion Subterm EqDec for context.
(* Instance ctxqDec : EqDec context.
Proof.
  intros [Γ L] [Γ' L'].
  destruct (eq_dec Γ Γ') as [<-|neΓ].
  destruct (eq_dec L L') as [<-|neL].
  + left; reflexivity.
  + right. intros e. apply neL. apply (f_equal Fctx e).
  + right. intros e. apply neΓ. apply (f_equal Tctx e).
Qed. *)

(* Inversions *)

Lemma wfcons_notin {L n b} : ell_wf (cons (Datatypes.pair n b) L) -> notin_ell L n.
Proof.
  simpl; intros wf.
  eapply lt_notin, wf.
Qed.

Definition wfFcons_new {L n b} : ell_wf (cons (Datatypes.pair n b) L) -> newnat L :=
  fun wfL => Build_newnat L n (squash (wfcons_notin wfL)).

Lemma wfFcons_wfF {L n b} : ell_wf (cons (Datatypes.pair n b) L) -> ell_wf L.
Proof.
  intros wf.
  eapply wf.
Qed.

(* 
 *)

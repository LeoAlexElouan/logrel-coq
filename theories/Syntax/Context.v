(** * LogRel.Syntax.Context: definition of contexts and operations on them.*)
From Stdlib Require Import ssreflect Morphisms Setoid Logic.StrictProp Lia.
From LogRel Require Import Utils BasicAst AutoSubst.Extra.
From Equations Require Import Equations.

Set Primitive Projections.

(** ** Context declaration *)
(** Context: list of declarations *)
(** Terms use de Bruijn indices to refer to context entries.*)
Inductive SOr (A B : SProp) : SProp :=
  | SOr_introl : A -> SOr A B
  | SOr_intror : B -> SOr A B.

Arguments SOr_introl {_ _}.
Arguments SOr_intror {_ _}.

Fixpoint in_ell (ℓ : ell_list) n b : SProp :=
  match ℓ with
  | nil => SFalse
  | cons (n', b') ℓ => SOr (SAnd (Squash (n = n')) (Squash (b = b'))) (in_ell ℓ n b)
  end.

Fixpoint notin_ell (ℓ : ell_list) n : SProp :=
  match ℓ with
  | nil => STrue
  | cons (n', _) ℓ => (SAnd (Squash (n <> n')) (notin_ell ℓ n))
  end.


Record newnat ℓ := {
  newnat_nat :> nat;
  newnat_new :> notin_ell ℓ newnat_nat;
  }.


Fixpoint cons_ell_list (ℓ : ell_list) (n : nat) (b : bool) : ell_list :=
  match ℓ as ℓ with
  | nil => cons (n, b) nil
  | cons (n', b') ℓ' => match Compare_dec.lt_dec n n' with
    | left _ => cons (n, b) ℓ
    | right _ => cons (n', b') (cons_ell_list ℓ' n b)
    end
  end.

Lemma lt_lt_ell ℓ n n': n < n' -> lt_ell n' ℓ -> lt_ell n ℓ.
Proof.
  intros ltn ltn'.
  induction ℓ as [| [n'' b''] ℓ ihℓ].
  + constructor.
  + cbn in *.
    constructor.
    - destruct ltn' as [[]]; constructor. lia.
    - now eapply ihℓ.
Qed.

Lemma lt_cons_ell (ℓ : ell_list) n' b' n : n < n' -> lt_ell n ℓ -> lt_ell n (cons_ell_list ℓ n' b').
Proof.
  intros ltnn' ltn.
  induction ℓ as [|[n'' b''] ℓ ihℓ].
  + simpl. repeat constructor; tea.
  + simpl in *.
    destruct (Compare_dec.lt_dec n' n'') as [ltn'n''| nltn'n''], ltn as [[ltnn''] ltn];
      repeat constructor; now simpl.
Qed.

Lemma Squash_dec P : Decidable.decidable P -> Squash P -> P.
Proof.
  intros [p|np] p'.
  + eapply p.
  + enough (H : SFalse) by destruct H.
    destruct p'. destruct (np p).
Qed.

Lemma Squash_neq (n n' : nat) : Squash (n <> n') -> n <> n'.
Proof.
  eapply Squash_dec,
    Decidable.dec_not, Peano_dec.dec_eq_nat.
Qed.

Lemma cons_ell_wf (ℓ : ell) (new : newnat ℓ) (b : bool) : ell_wf (cons_ell_list ℓ new b).
Proof.
  destruct ℓ as [ℓ wf], new as [n new]; cbn in *.
  induction ℓ as [|[n' b'] ℓ].
  + simpl. easy.
  + simpl.
    destruct (Compare_dec.lt_dec n n') as [ltnn'| nltnn']; simpl in *.
    - repeat constructor; try easy.
      now eapply lt_lt_ell.
    - constructor.
      * eapply lt_cons_ell, wf.
        destruct new as [ne%Squash_neq new].
        lia.
      * now eapply IHℓ.
Qed.

Definition cons_ell (ℓ: ell) (new : newnat ℓ) b : ell
  := Build_ell (cons_ell_list ℓ new b) (cons_ell_wf _ _ _).

Notation "A <->S B " := (SAnd (A -> B) (B -> A)) (at level 50).

Lemma in_cons_ell {ℓ new b' n b} : in_ell (cons_ell ℓ new b') n b <->S (SOr (SAnd (Squash (n = new)) (Squash (b = b'))) (in_ell ℓ n b)).
Proof.
  destruct new as [n' new], ℓ as [ℓ wf]; cbn in *.
  induction ℓ as [| [n'' b''] ℓ IHℓ]. 
  + cbn. constructor; intros H; eapply H.
  + cbn in *.
    destruct (Compare_dec.lt_dec n' n'').
    - cbn. constructor; intros H; eapply H.
    - cbn.
      specialize (IHℓ ltac:(destruct wf; tea) ltac:(eapply new)).
      constructor.
      * intros [ | [ | ]%IHℓ]; [right; left |left | right; right]; tea.
      * intros [ | [ | ]].
       ++ right. eapply IHℓ; left; tea.
       ++ left; tea.
       ++ right. eapply IHℓ; right; tea.
Qed.

Lemma in_cons_ell_head {ℓ new b} : in_ell (cons_ell ℓ new b) new b.
Proof.
  eapply in_cons_ell.
  left.
  repeat constructor.
Qed.


Notation nil_ell := (Build_ell nil stt).



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

Definition index_to_nat {A}  : forall {l : list A}, list_index l -> nat := index_induction _ (fun _ _ => 0) (fun _ _ _ => S).

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
Instance ren_decl : Ren1 (nat -> nat) decl decl | 2 := fun ρ d =>
  match d with
  | term_decl t => term_decl t⟨ρ⟩
  | ell_decl ℓ => ell_decl ℓ
  end.
(* Instance ren_to_decl {X} `{Ren1 X term term} : Ren1 X term decl | 3 :=
  fun ρ t => term_decl t⟨ρ⟩.
Instance subst_to_decl {X} `{Subst1 X term term} : Subst1 X term decl | 3 :=
  fun σ t => term_decl t[σ]. *)
#[global]
Instance ren_decl_morphism : Proper ((`=1`) ==> eq ==> eq) ren_decl.
Proof.
  intros ρl ρr ρeq [t|ℓ] dr <-; simpl.
  + now rewrite ρeq.
  + reflexivity.
Qed.
Definition ren_alpha_decl ρ d :=
  match d with 
  | term_decl t => term_decl (ren_alpha ρ t)
  | ell_decl ℓ => ell_decl ℓ
  end.
#[global]
Instance ren_alpha_decl_morphism : Proper ((`=1`) ==> eq ==> eq) ren_alpha_decl.
Proof.
  intros ρl ρr ρeq [t|ℓ] dr <-; simpl.
  + now rewrite ρeq.
  + reflexivity.
Qed.

#[global] Instance Ren2_alpha_decl {X : Type} `{Ren1 X decl decl} :
  (Ren2 X (nat -> nat) decl decl) :=
  fun ρ ρε d => (ren_alpha_decl ρε d)⟨ρ⟩.

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
Notation " Γ ,, d " := (Build_context (@cons decl d (Tctx Γ)) (Fctx Γ)) (at level 20, d at next level).
Notation " Γ ,, i : new ↦ b " := (Build_context (Tctx Γ) (Fcons (Fctx Γ) i new b)) (at level 20, new at next level, b at next level).
Notation " Γ ,, ↦ F" := (Build_context (List.map (ren_alpha_decl S) (Tctx Γ)) (cons F (Fctx Γ))).
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
  | is_in b : in_ell L n b -> decide_in_type L n
  | is_notin : notin_ell L n -> decide_in_type L n.

Arguments is_in {_ _}.
Arguments is_notin {_ _}.

Lemma decide_in L n : decide_in_type L n.
Proof.
  induction L as [|[n' b'] L [b hin|hnotin]].
  - right.
    repeat constructor.
  - apply (is_in b). now right.
  - pose proof (PeanoNat.Nat.eq_dec n n') as e.
    destruct e as [<-|].
    + apply (is_in b').
      repeat constructor.
    + now right; cbn; repeat constructor.
Qed.

Lemma notin_is_not_in {L n b} : notin_ell L n -> in_ell L n b -> SFalse.
Proof.
  intros hnotin hin.
  induction L as [|[n' b'] L ihL].
  + destruct hin.
  + simpl in *.
    destruct hin.
    - now destruct hnotin as [[ne] _],
        s as [[e] _].
    - easy.
Qed.

Lemma not_in_is_notin' {L n} : (in_ell L n true -> SFalse) -> (in_ell L n false -> SFalse) -> notin_ell L n.
Proof.
  intros hnotint hnotinf.
  induction L as [|[n' b'] L ihL].
  + constructor.
  + simpl in *.
    constructor.
    - repeat constructor. intros <-.
      assert SFalse as [].
      destruct b'.
      * eapply hnotint; repeat constructor.
      * eapply hnotinf; repeat constructor.
    - eapply ihL; intros inL.
      * eapply hnotint; right; eapply inL.
      * eapply hnotinf; right; eapply inL.
Qed.

Lemma not_in_is_notin {L n} : (forall b, in_ell L n b -> SFalse) -> notin_ell L n.
Proof.
  intros.
  now eapply not_in_is_notin'.
Qed.

Lemma lt_notin ℓ n : lt_ell n ℓ -> notin_ell ℓ n.
Proof.
  induction ℓ as [|[n' b'] ℓ ihℓ]; simpl; constructor.
  + destruct H as [[]]; repeat constructor. lia.
  + easy.
Qed.

Lemma functionality_inversion (L : ell) n : in_ell L n true -> in_ell L n false -> SFalse.
Proof.
  intros int inf.
  destruct L as [L wfL].
  induction L as [|[n' b'] L ihL] in wfL, int, inf |-*; simpl in *.
  {destruct int. }
  destruct int as [[[->] [<-]] |int], inf as [[[en] [eb]]| inf].
  + inversion eb.
  + eapply notin_is_not_in, inf.
    now eapply lt_notin.
  + destruct en. eapply notin_is_not_in, int.
    now eapply lt_notin.
  + eapply ihL; try easy; constructor; easy.
Qed.

Lemma functionality (L:ell) n b b': in_ell L n b -> in_ell L n b' -> b = b'.
Proof.
  intros hin hin'.
  destruct L as [L wfL].
  destruct b, b'; auto.
  all: enough (H : SFalse) by destruct H;
    now eapply functionality_inversion.
Qed.

(* Lemma decide_in_irr (ℓ : ell) n (in1 in2 : decide_in_type ℓ n) : in1 = in2.
Proof.
  destruct in1, in2.
  + destruct (functionality _ _ _ _ (squash i) (squash i0)).
    f_equal.
    destruct ℓ as [ℓ wf].
    induction ℓ as [| [n' b'] ℓ ihℓ]; cbn in *.
    - destruct i.
    - destruct i, i0.
      * f_equal.
        destruct a, a0; f_equal.
       ++ enough (H : UIP nat) by eapply H.
        typeclasses eauto.
       ++ enough (H : UIP bool) by eapply H.
        typeclasses eauto.
      * enough (H : SFalse) by destruct H.
        destruct wf, a as [<- <-]. eapply notin_is_not_in, i. 
        eapply lt_notin, a0.
      * enough (H : SFalse) by destruct H.
        destruct wf, a as [<- <-]. eapply notin_is_not_in, i. 
        eapply lt_notin, a0.
      * f_equal.
        eapply ihℓ.
        destruct wf. now constructor.
  + enough (H : SFalse) by destruct H.
    now eapply notin_is_not_in.
  + enough (H : SFalse) by destruct H.
    now eapply notin_is_not_in.
  + f_equal.
    destruct ℓ as [ℓ wf].
    induction ℓ as [| [n' b'] ℓ ihℓ]; cbn in *.
    - now destruct n0, n1.
    - destruct n0, n1; f_equal.
      * now destruct b, b0; f_equal.
      * eapply ihℓ.
        destruct wf; now constructor.
Qed. *)

Lemma decide_in_in (L : ell) n b (hin : in_ell L n b) :
  decide_in L n = is_in b hin.
Proof.
  destruct (decide_in L n) as [b' hin'|hnotin].
  - now destruct (functionality L n b b' hin hin').
  - enough (H : SFalse) by destruct H.
    destruct (notin_is_not_in hnotin hin).
Qed.

Lemma decide_in_new (L : ell) (new : newnat L) :
  decide_in L new = is_notin new.
Proof.
  destruct (decide_in L new) as [b hin|hnotin].
  - enough (H : SFalse) by destruct H.
(*     destruct hin as [hin]. *)
    destruct new as [n new].
    now eapply notin_is_not_in.
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

Lemma wfcons_notin {L n b} : ell_wf (cons (n, b) L) -> notin_ell L n.
Proof.
  simpl; intros wf.
  eapply lt_notin, wf.
Qed.

Definition wfFcons_new {L n b} : ell_wf (cons (n, b) L) -> newnat L :=
  fun wfL => Build_newnat L n (wfcons_notin wfL).

Lemma wfFcons_wfF {L n b} : ell_wf (cons (n, b) L) -> ell_wf L.
Proof.
  intros wf.
  eapply wf.
Qed.

Variant neVar := termNe | ellNe (k v : nat).


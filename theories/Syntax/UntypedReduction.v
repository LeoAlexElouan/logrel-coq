(** * LogRel.Syntax.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils AutoSubst.Extra Notations.
From Equations Require Import Equations. (* for depelim *)
From LogRel.Syntax Require Import BasicAst Context NormalForms (* Weakening *) Computations.

(** ** Reductions *)

(** *** One-step reduction. *)

Fixpoint whns_all {red : term -> term -> Type} (Pred : forall t t', red t t' -> Type)
  {k v t} (w : @whns red k v t) {struct w} : Type :=
  match w with
  | whns_tEval notink => unit
  | whns_tApp w => whns_all Pred w
  | whns_tNatElim w => whns_all Pred w
  | whns_tBoolElim w => whns_all Pred w
  | whns_tEmptyElim w => whns_all Pred w
  | whns_tTreeElim w => whns_all Pred w
  | whns_tFst w => whns_all Pred w
  | whns_tSnd w => whns_all Pred w
  | whns_tIdElim w => whns_all Pred w
  | whns_tAlpha w => whns_all Pred w
  | whns_tXi w => whns_all Pred w
  | whns_tXXi w => whns_all Pred w
  | whns_tXXiRed w notink' r w'=> whns_all Pred w × Pred _ _ r × whns_all Pred w'
  end.

Fixpoint whns_all_forall red Pred : (forall t t' (r : red t t'), Pred _ _ r) ->
  forall k v t (w : @whns red k v t), whns_all Pred w.
Proof.
  intros allr k v t w.
  destruct w.
  2-12: cbn; eapply whns_all_forall, allr.
  + constructor.
  + repeat constructor.
    - eapply whns_all_forall, allr.
    - eapply allr.
    - eapply whns_all_forall, allr.
Defined.


Inductive closure (R : term -> term -> Type) : term -> term -> Type :=
  | clos_nil t : closure R t t
  | clos_cons t t' u : closure R t' u -> R t t' -> closure R t u.

Fixpoint closure_all {R : term -> term -> Type} (PR : forall t t', R t t' -> Type)
  {t t'} (rtt' : closure R t t') {struct rtt'} : Type :=
  match rtt' with
  | clos_nil _ t => unit
  | clos_cons _ t t' u rt'u rtt' => closure_all PR rt'u × PR _ _ rtt'
  end.

Fixpoint closure_all_forall R PR : (forall t t' (rtt' : R t t'), PR _ _ rtt') -> forall t t' (rtt' : closure R t t'), closure_all PR rtt'.
Proof.
  intros allr t t' rtt'.
  destruct rtt'; constructor.
  - eapply closure_all_forall, allr.
  - eapply allr.
Defined.



Inductive OneRedAlg {L : list ell} : term -> term -> Type :=
| BRed {A a t} :
    [ L | tApp (tLambda A t) a ⤳ t[a..] ]
| appSubst {t u a} :
    [ L |t ⤳ u ] ->
    [ L |tApp t a ⤳ tApp u a ]
| natElimSubst {P hz hs n n'} :
    [ L |n ⤳ n' ] ->
    [ L |tNatElim P hz hs n ⤳ tNatElim P hz hs n' ]
| natElimZero {P hz hs} :
    [ L |tNatElim P hz hs tZero ⤳ hz ]
| natElimSucc {P hz hs n} :
    [ L |tNatElim P hz hs (tSucc n) ⤳ tApp (tApp hs n) (tNatElim P hz hs n) ]
| boolElimSubst {P ht hf n n'} :
    [ L |n ⤳ n' ] ->
    [ L |tBoolElim P ht hf n ⤳ tBoolElim P ht hf n' ]
| boolElimTrue {P ht hf} :
    [ L |tBoolElim P ht hf tTrue ⤳ ht ]
| boolElimFalse {P ht hf} :
    [ L |tBoolElim P ht hf tFalse ⤳ hf ]
| alphaSubst {i k n n'} :
  [ L | n ⤳ n' ] -> [ L | tApp (tAlpha i) (nSucc k n) ⤳ tApp (tAlpha i) (nSucc k n') ]
(* | alphaSubstSucc {i n n'} :
  [ L | tApp (tAlpha i) n ⤳ tApp (tAlpha i) n' ] ->
  [ L | tApp (tAlpha i) (tSucc n) ⤳ tApp (tAlpha i) (tSucc n') ] *)
| alphaRed {i n b} (hin : in_ell (list_at L i) n b) :
  [ L | tApp (tAlpha (index_to_nat i)) (nat_to_term n) ⤳ bool_to_term b]
| emptyElimSubst {P e e'} :
    [L |e ⤳ e'] ->
    [L |tEmptyElim P e ⤳ tEmptyElim P e']
| treeElimSubst {P hl hn t t'} :
    [ L |t ⤳ t' ] ->
    [ L |tTreeElim P hl hn t ⤳ tTreeElim P hl hn t' ]
| treeElimLeaf {P hl hn n} :
    [ L |tTreeElim P hl hn (tLeaf n) ⤳ tApp hl n ]
| treeElimNode {P hl hn n tl tr} :
    [ L |tTreeElim P hl hn (tNode n tl tr) ⤳
      tApp (tApp (tApp (tApp (tApp hn n) tl) tr) (tTreeElim P hl hn tl)) (tTreeElim P hl hn tr) ]
| fstSubst {p p'} :
    [ L |p ⤳ p'] ->
    [ L |tFst p ⤳ tFst p']
| fstPair {A B a b} :
    [ L |tFst (tPair A B a b) ⤳ a ]
| sndSubst {p p'} :
    [ L |p ⤳ p'] ->
    [ L |tSnd p ⤳ tSnd p']
| sndPair {A B a b} :
    [ L |tSnd (tPair A B a b) ⤳ b ]
| idElimRefl {A x P hr y A' z} :
  [ L |tIdElim A x P hr y (tRefl A' z) ⤳ hr ]
| idElimSubst {A x P hr y e e'} :
  [L |e ⤳ e'] ->
  [ L |tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]
| evalRel v k b (ℓ : ell) : in_ell ℓ k b ->
  [ L |tApp (tEval ℓ (tRel v)) (nat_to_term k) ⤳ (bool_to_term b) ]
| evalBox ℓ ℓ' t : [ L | tEval ℓ (tBox ℓ' t) ⤳ t]
| xiSubst ℓ n n' k : [L | n ⤳ n'] -> [L | tXi ℓ (nSucc k n) ⤳ tXi ℓ (nSucc k n')]
| xiLeaf ℓ n : [L | tXi ℓ (nat_to_term n) ⤳ tLeaf (nat_to_term n) ]
| xiNode (ℓ : ell) n (k : newnat ℓ) : whns (red := closure OneRedAlg) k 0 n ->
  [L |tXi ℓ n ⤳ tNode (nat_to_term k) (tXi (cons_ell ℓ k true) n) (tXi (cons_ell ℓ k false) n) ]
| xxiSubst ℓ m m' n k : [L | m ⤳ m'] -> [L | tXXi ℓ (nSucc k m) n ⤳ tXXi ℓ (nSucc k m') n]

where "[ L | t ⤳ t' ]" := (@OneRedAlg L t t') : typing_scope.

Fixpoint OneRedAlg_rect_with_all
  (L : list ell) (P : forall t t0 : term, [L | t ⤳ t0] -> Type)
  (hBRed : forall A a t : term, P (tApp (tLambda A t) a) t[a..] BRed)
  (happSubst : forall (t u a : term) (o : [L | t ⤳ u]), P t u o -> P (tApp t a) (tApp u a) (appSubst o))
  (hnatElimSubst : forall (P0 hz hs n n' : term) (o : [L | n ⤳ n']),
   P n n' o -> P (tNatElim P0 hz hs n) (tNatElim P0 hz hs n') (natElimSubst o))
  (hnatElimZero : forall P0 hz hs : term, P (tNatElim P0 hz hs tZero) hz natElimZero)
  (hnatElimSucc : forall P0 hz hs n : term,
   P (tNatElim P0 hz hs (tSucc n)) (tApp (tApp hs n) (tNatElim P0 hz hs n)) natElimSucc)
  (hboolElimSubst : forall (P0 ht hf n n' : term) (o : [L | n ⤳ n']),
   P n n' o -> P (tBoolElim P0 ht hf n) (tBoolElim P0 ht hf n') (boolElimSubst o))
  (hboolElimTrue : forall P0 ht hf : term, P (tBoolElim P0 ht hf tTrue) ht boolElimTrue)
  (hboolElimFalse : forall P0 ht hf : term, P (tBoolElim P0 ht hf tFalse) hf boolElimFalse)
  (halphaSubst : forall (i k : nat) (n n' : term) (o : [L | n ⤳ n']),
   P n n' o -> P (tApp (tAlpha i) (nSucc k n)) (tApp (tAlpha i) (nSucc k n')) (alphaSubst o))
  (halphaRed : forall (i : list_index L) (n : nat) (b : bool) (hin : in_ell (list_at L i) n b),
   P (tApp (tAlpha i) (nat_to_term n)) (bool_to_term b) (alphaRed hin))
  (hemptyElimSubst : forall (P0 e e' : term) (o : [L | e ⤳ e']),
   P e e' o -> P (tEmptyElim P0 e) (tEmptyElim P0 e') (emptyElimSubst o))
  (htreeElimSubst : forall (P0 hl hn t t' : term) (o : [L | t ⤳ t']),
   P t t' o -> P (tTreeElim P0 hl hn t) (tTreeElim P0 hl hn t') (treeElimSubst o))
  (htreeElimLeaf : forall P0 hl hn n : term, P (tTreeElim P0 hl hn (tLeaf n)) (tApp hl n) treeElimLeaf)
  (htreeElimNode : forall P0 hl hn n tl tr : term,
   P (tTreeElim P0 hl hn (tNode n tl tr))
     (tApp (tApp (tApp (tApp (tApp hn n) tl) tr) (tTreeElim P0 hl hn tl)) (tTreeElim P0 hl hn tr))
     treeElimNode)
  (hfstSubst : forall (p p' : term) (o : [L | p ⤳ p']), P p p' o -> P (tFst p) (tFst p') (fstSubst o))
  (hfstPair : forall A B a b : term, P (tFst (tPair A B a b)) a fstPair)
  (hsndSubst : forall (p p' : term) (o : [L | p ⤳ p']), P p p' o -> P (tSnd p) (tSnd p') (sndSubst o))
  (hsndPair : forall A B a b : term, P (tSnd (tPair A B a b)) b sndPair)
  (hidElimRefl : forall A x P0 hr y A' z : term, P (tIdElim A x P0 hr y (tRefl A' z)) hr idElimRefl)
  (hidElimSubst : forall (A x P0 hr y e e' : term) (o : [L | e ⤳ e']),
   P e e' o -> P (tIdElim A x P0 hr y e) (tIdElim A x P0 hr y e') (idElimSubst o))
  (hevalRel : forall (v k : nat) (b : bool) (ℓ : ell) (i : in_ell ℓ k b),
   P (tApp (tEval ℓ (tRel v)) (nat_to_term k)) (bool_to_term b) (evalRel v k b ℓ i))
  (hevalBox : forall (ℓ ℓ' : ell) (t : term), P (tEval ℓ (tBox ℓ' t)) t (evalBox ℓ ℓ' t))
  (hxiSubst : forall (ℓ : ell) (n n' : term) k (o : [L | n ⤳ n']),
   P n n' o -> P (tXi ℓ (nSucc k n)) (tXi ℓ (nSucc k n')) (xiSubst ℓ n n' k o))
  (hxiLeaf : forall (ℓ : ell) (n : nat), P (tXi ℓ (nat_to_term n)) (tLeaf (nat_to_term n)) (xiLeaf ℓ n))
  (hxiNode : forall (ℓ : ell) (n : term) (k : newnat ℓ) (w : whns k 0 n), whns_all (fun t t' => closure_all P) w ->
   P (tXi ℓ n) (tNode (nat_to_term k) (tXi (cons_ell ℓ k true) n) (tXi (cons_ell ℓ k false) n))
     (xiNode ℓ n k w))
  (hxxiSubst : forall (ℓ : ell) (m m' n : term) (k : nat) (o : [L | m ⤳ m']), P m m' o ->
   P (tXXi ℓ (nSucc k m) n) (tXXi ℓ (nSucc k m') n) (xxiSubst ℓ m m' n k o))
  (t t0 : term) (o : [L | t ⤳ t0]) {struct o}: P t t0 o.
Proof.
  destruct o.
  + eapply hBRed.
  + eapply happSubst, OneRedAlg_rect_with_all; tea.
  + eapply hnatElimSubst, OneRedAlg_rect_with_all; tea.
  + eapply hnatElimZero.
  + eapply hnatElimSucc.
  + eapply hboolElimSubst, OneRedAlg_rect_with_all; tea.
  + eapply hboolElimTrue.
  + eapply hboolElimFalse.
  + eapply halphaSubst, OneRedAlg_rect_with_all; tea.
  + eapply halphaRed.
  + eapply hemptyElimSubst, OneRedAlg_rect_with_all; tea.
  + eapply htreeElimSubst, OneRedAlg_rect_with_all; tea.
  + eapply htreeElimLeaf.
  + eapply htreeElimNode.
  + eapply hfstSubst, OneRedAlg_rect_with_all; tea.
  + eapply hfstPair.
  + eapply hsndSubst, OneRedAlg_rect_with_all; tea.
  + eapply hsndPair.
  + eapply hidElimRefl.
  + eapply hidElimSubst, OneRedAlg_rect_with_all; tea.
  + eapply hevalRel.
  + eapply hevalBox.
  + eapply hxiSubst, OneRedAlg_rect_with_all; tea.
  + eapply hxiLeaf.
  + eapply hxiNode, whns_all_forall, closure_all_forall, OneRedAlg_rect_with_all; tea.
  + eapply hxxiSubst, OneRedAlg_rect_with_all; tea.
Qed.


(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Definition RedClosureAlg {L : list ell} : term -> term -> Type := closure (@OneRedAlg L).
(*   | redIdAlg {t} :
    [ L | t ⤳* t ]
  | redSuccAlg {t t' u} :
    [ L | t ⤳ t'] ->
    [ L | t' ⤳* u ] ->
    [ L | t ⤳* u ]
  where *)
Notation "[ L | t ⤳* t' ]" := (@RedClosureAlg L t t') : typing_scope.

Equations Derive Signature for OneRedAlg.
Equations Derive Signature for closure.


#[export] Instance RedAlgTrans {L} : PreOrder (RedClosureAlg (L:=L)).
  Proof.
    split.
    - now econstructor.
    - intros * ; induction 1.
      1: easy.
      intros.
      now econstructor.
  Qed.

(** *** Co-reduction *)
(** The symmetric of reduction, in Prop. The well-founded relation on which the reduction
  machine operates. *)

Record cored L t t' : Prop := { _ : [L |t' ⤳ t] }.

(** ** Properties *)

(** *** Weak-head normal forms do not reduce *)

Ltac inv_whne :=
  match goal with [ H : whne _ |- _ ] => inversion H end.


Lemma whne_nored {L} n u :
  @whne (@RedClosureAlg L) n -> [ L | n ⤳ u] -> False.
Proof.
  intros ne red.
  induction ne in u, red |-*.
  1-13: inversion red; subst; clear red.
  all: try now inversion ne.
  * inversion X.
  * eapply nSucc_eq_inv in H1 as [[<- <-]| [(n0&->&<-)|(n0&<-&->)]].
    - easy.
    - inversion X.
    - inversion ne.
  * eapply nSucc_nat_to_term in H1 as [[] <-];
    inversion ne.
  * eapply nSucc_eq_inv in H1 as [[<- <-]| [(?&->&<-)|(?&<-&->)]].
    - easy.
    - inversion X.
    - inversion ne.
  * eapply nSucc_nat_to_term in H1 as [[] <-];
    inversion ne.
  * destruct k.
    - admit.
    - inversion X.
Admitted.

Ltac inv_alpha :=
  match goal with
    [ H : [_ | tAlpha _ ⤳ _] |- _ ] => inversion H
    | [ H : whne (tAlpha _) |- _ ] => inversion H end.
(* Lemma whnf_nored L n u :
  @whnf (@RedClosureAlg L) n -> [ L | n ⤳ u] -> False.
Proof.
  intros nf red.
  induction nf.
  all: try now inversion red.
  now eapply whne_nored.
  admit.
Admitted.
 *)
(** *** Determinism of reduction *)

Lemma ored_detaux : forall {L i i' n n'}, [ L | tApp (tAlpha i) (nat_to_term n) ⤳ tApp (tAlpha i') n'] -> False.
Proof.
  intros L i i' n n' H.
  inversion H; subst; clear H.
  * inversion X.
  * eapply eq_sym, nSucc_nat_to_term in H2 as [[] <-].
    - inversion X.
    - inversion X.
  * destruct b; inversion H3.
Qed.

#[local] Ltac nSucc_handler :=
try match goal with
| eq : nSucc ?k ?t = nSucc ?k' ?t' |- _ =>
    eapply nSucc_eq_inv in eq as [[<- <-] | [(?&->&<-)|(?&<-&->)]]
| eq : nSucc ?k ?t  = nat_to_term ?k' |- _ =>
    eapply symmetry, nSucc_nat_to_term in eq as [[] <-]
| eq : nat_to_term ?k = nSucc ?k' ?t' |- _ =>
    eapply nSucc_nat_to_term in eq as [[] <-]
| eq  : nat_to_term ?k =  nat_to_term ?k' |- _ =>
    eapply nat_to_term_inj in eq as <-
end.

(* Lemma det_closure L t n k v (r : [ L | t ⤳* n ]) : @whns (@RedClosureAlg L) k v n ->
  closure_all (fun t u _ => (forall v, [L | t ⤳ v] -> u = v) /\
    (forall k v : nat, @whns (@RedClosureAlg L) k v t -> False)) r ->
    forall n' k' v', @whns (@RedClosureAlg L) k' v' n' ->[L | t ⤳* n' ] -> n = n'.
Proof.
  intros w allr ??? w' r'.
  induction r; inversion r'; subst; clear r'.
  + reflexivity.
  + cbn in allr. *)
Goal forall L t, (forall u, [L | t ⤳ u] -> forall k v, @whns (@RedClosureAlg L) k v t -> False) ->
  (forall u, [L | t ⤳* u] -> forall k v, @whns (@RedClosureAlg L) k v t -> t = u).
Proof.
  intros.
  induction X.
  reflexivity.
  exfalso; eauto.
Qed.

(* Lemma wk_det L t n (r : [L | t ⤳* n]) :
  (forall u, [L | t ⤳* u] ->forall k v, @whns (@RedClosureAlg L) k v t -> t = u) ->
  closure_all (fun t u _ => (forall v, [L | t ⤳ v] -> u = v) /\
    (forall k v : nat, @whns (@RedClosureAlg L) k v t -> False)) r ->
  closure_all (fun t _ _ =>
    forall u, [L | t ⤳* u] ->forall k v, @whns (@RedClosureAlg L) k v t -> t = u) r.
Proof.
  intros.
  induction r.
  + cbn in *. constructor.
  + constructor.
    - eapply IHr; clear IHr.
      * cbn in X.
        destruct r.
       ++ cbn in *.
          intros. *)

Definition instant_det {L} t u (r : [L | t ⤳ u]) := (forall u', [L | t ⤳ u'] -> u = u')
  /\ (forall k v, @whns (closure (@OneRedAlg L)) k v t -> False).



Lemma whs_det L t n (r : [L | t ⤳* n]) :
  (forall u (r : [L | n ⤳ u]), instant_det n u r) ->
  closure_all (instant_det (L:=L)) r ->
  forall k v, @whns (@RedClosureAlg L) k v n ->
  forall n', [L | t ⤳* n'] ->
  forall k' v', @whns (@RedClosureAlg L) k' v' n' ->
  n = n'.
Proof.
  intros tdet allr ?? w ? r' ?? w'.
  induction r; inversion r'; subst; clear r'.
  + reflexivity.
  + exfalso.
    specialize (tdet _ X0) as []. eauto.
  + destruct allr as (allr&hred&hwhns).
    exfalso. eauto.
  + destruct allr as (allr&hred&hwhns).
    eapply IHr; tea.
    now destruct (hred _ X0).
Qed.


Lemma whns_uniq_k L k v t (w : @whns (closure (@OneRedAlg L)) k v t) :
  whns_all (fun _ _ => closure_all (instant_det (L:=L))) w ->
  forall k', @whns (closure (@OneRedAlg L)) k' v t -> k = k'.
Proof.
(*   intros allw ? w'.
  induction w' in k, w, allw |-*; revert allw; dependent inversion w; subst; cbn; clear w; intros ?; nSucc_handler; eauto.
  all : try solve [inversion w'| inversion w0].
  + admit.
  + admit.
  + inversion w'1.
  + destruct (IHw'1 _ w0 ltac:(eapply allw)).
    
    eapply IHw'2.
   destruct allw; eapply IHw'; tea. specialize (IHw' _ _ _ allw) as [<- ev].
    now inversion ev.
  + specialize (IHw' _ _ _ allw) as [<- ev].
    now inversion ev.
  + destruct allw as (allw1&hr&allw2).
    specialize (IHw' _ _ _ allw1) as [<- ev].
    now inversion ev.
  + specialize (IHw'1 _ _ _ allw) as [<- ev].
    now inversion ev.
  + inversion w'1.
  + destruct allw as (allw0&allc&allw1).
    assert (forall t' (r : [L | n' ⤳ t']), instant_det n' t' r).
    { intros.
      split.
      - intros. *)
Admitted.


Lemma whns_uniq_kv L k v t (w : @whns (closure (@OneRedAlg L)) k v t) :
  whns_all (fun _ _ => closure_all (instant_det (L:=L))) w ->
  forall k' v', @whns (closure (@OneRedAlg L)) k' v' t -> k = k' /\ v = v'.
Proof.
  intros allw ?? w'.
  induction w' in k, v, w, allw |-*; revert allw; dependent inversion w; subst; cbn; clear w; intros ?; nSucc_handler; eauto.
  all : try solve [inversion w'| inversion w0].
  + specialize (IHw' _ _ _ allw) as [<- ev].
    now inversion ev.
  + specialize (IHw' _ _ _ allw) as [<- ev].
    now inversion ev.
  + destruct allw as (allw1&hr&allw2).
    specialize (IHw' _ _ _ allw1) as [<- ev].
    now inversion ev.
  + specialize (IHw'1 _ _ _ allw) as [<- ev].
    now inversion ev.
  + inversion w'1.
  + destruct allw as (allw0&allc&allw1).
    assert (forall t' (r : [L | n' ⤳ t']), instant_det n' t' r).
    { intros.
      split.
      - intros.

Admitted.

Lemma ored_no_whns {L t u} :
  [L | t ⤳ u] -> forall k v, @whns (@RedClosureAlg L) k v t -> False.
Proof.
  intros red k v w.
  induction red using OneRedAlg_rect_with_all in k, v, w |-*;
    inversion w; subst; clear w; nSucc_handler; eauto.
  all: try solve [inversion X |inversion red].
  * destruct (notin_is_not_in ltac:(tea) ltac:(tea)).
  * destruct k'.
    2: inversion w0.
    cbn in w0.
    admit.
Admitted.

Lemma ored_det {L t u} :
  [L | t ⤳ u] -> (forall v, [L | t ⤳ v] ->
  u = v) /\ (forall k v, @whns (@RedClosureAlg L) k v t -> False).
Proof.
  intros red.
  induction red using OneRedAlg_rect_with_all; try destruct IHred as [IHredred IHredwhns].
  1-26 : split;
    [intros t_r red'; inversion red'; subst; clear red'; nSucc_handler; repeat f_equal; eauto
    |intros k_w v_w wt; inversion wt; subst; clear wt; nSucc_handler; eauto]; try solve [inversion X | inversion red].
  * eapply index_to_nat_inj in H0 as <-.
    eapply functionality; tea.
  * eapply functionality; tea.
  * destruct (notin_is_not_in H0 i).
  * destruct k.
    2: inversion X.
    destruct (IHredwhns _ _ X).
  * destruct n; inversion X.
  * destruct k0.
    2: inversion w.
    exfalso; cbn in *.
    induction w in X, n', X0 |-* ; inversion X0; subst; clear X0; nSucc_handler.
    all: try solve [inversion X1 | inversion w | eapply IHw; tea].
    + destruct (notin_is_not_in n H3).
    + destruct k'.
      2: inversion X1.
      cbn in *.
      specialize (IHw X).
      admit.
    + destruct X as (?&?&?).
      eapply IHw1; tea.
    + inversion w1.
  * destruct n0; inversion w.
  * admit.
  * admit.
  * admit.
  * destruct k'.
    2: inversion w.
    cbn in w.
Admitted.

Lemma red_whne {L} t u : [ L | t ⤳* u] -> whne t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma red_whnf {L} t u : [L | t ⤳* u] -> whnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma whred_red_det {L} t u u' :
  whnf u ->
  [L | t ⤳* u] -> [L | t ⤳* u'] ->
  [ L | u' ⤳* u].
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_whnf in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.

Corollary whred_det {L} t u u' :
  whnf u -> whnf u' ->
  [L | t ⤳* u] -> [L | t ⤳* u'] ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

(** *** Stability by weakening *)
Lemma oFredalg L L' (wρε : well_Fweakening L' L) t u: 
  [L | t ⤳ u] -> [L' | (* ren_alpha ρε *) t ⤳ (* ren_alpha ρε *) u].
Proof.
  intros hred.
  induction hred.
  all: try now constructor.
  rewrite <- ren_index_to_ren with (wρε := wρε).
  constructor.
  eapply well_Fwk_in. , hin.
  2-10, 12-21: now constructor.
  - rewrite subst_ren_alpha. constructor.
  - cbn.
    rewrite nat_to_term_ren_alpha, bool_to_term_ren_alpha,
      <- ren_index_to_ren with (wρε:=wρε).
    eapply alphaRed.
    eapply well_Fwk_in, hin.
Defined.

Lemma oredalg_wk (ρ : nat -> nat) L (t u : term) :
  [L | t ⤳ u] ->
  [L | t⟨ρ⟩ ⤳ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  2-9,12-21:cbn; now econstructor.
  - cbn. rewrite subst_ren_up.
    constructor.
  - cbn. eapply alphaSubstSucc, IHHred.
  - cbn. rewrite nat_to_term_ren, bool_to_term_ren.
    now econstructor.
Qed.
(* 
Lemma oredalg_str (Γ Δ : context) (ρ : Δ ≤ Γ) (t u : term) :
  [t⟨ρ⟩ ⤳ u] ->
  ∑ u', u = u'⟨ρ⟩ × [t ⤳ u'].
Proof.
  intros Hred.
  remember t⟨ρ⟩ as t' eqn:eqt in *.
  induction Hred in t, eqt |- *.
  all: repeat match goal with
    | eq : _ = ?t⟨_⟩ |- _ =>
        destruct t ; cbn in * ; try solve [congruence] ;
        inversion eq ; subst ; clear eq
  end.
  all: try (edestruct IHHred as [? [->]]; [reflexivity|..]).
  all: eexists ; split ; cycle -1 ; [now econstructor | now bsimpl].
Qed. *)

Lemma cFredalg L L' ρε (wρε : well_Fweakening ρε L' L) t u: 
  [L | t ⤳* u] -> [L' | ren_alpha ρε t ⤳* ren_alpha ρε u].
Proof.
  induction 1; econstructor; eauto using oFredalg.
Defined.

Lemma credalg_wk (ρ : nat -> nat) {L} (t u : term) :
[L|t ⤳* u] ->
[L|t⟨ρ⟩ ⤳* u⟨ρ⟩].
Proof.
  induction 1 ; econstructor ; eauto using oredalg_wk.
Qed.

Lemma credalg_Fwk (Γ Δ : context) (ρ : Δ ≤ Γ) (t u : term) :
[Γ|t ⤳* u] ->
[Δ | t⟨ρ⟩ ⤳* u⟨ρ⟩].
Proof.
  intros. eapply credalg_wk, cFredalg, H. eapply ρ.
Qed.
(* 
Lemma credalg_str (Γ Δ : context) (ρ : Δ ≤ Γ) (t u : term) :
  [t⟨ρ⟩ ⤳* u] ->
  ∑ u', u = u'⟨ρ⟩ × [t ⤳* u'].
Proof.
  intros Hred.
  remember t⟨ρ⟩ as t' eqn:eqt in *.
  induction Hred in t, eqt |- *.
  - eexists ; split ; tea.
    now constructor.
  - subst.
    eapply oredalg_str in o as [? [-> ]].
    edestruct IHHred as [? [->]]; [reflexivity|..].
    eexists ; split ; [reflexivity|..].
    now econstructor.
Qed. *)

(** Derived rules *)

Lemma redalg_app {L t t' u} : [ L | t ⤳* t'] -> [ L | tApp t u ⤳* tApp t' u].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_natElim {L P hs hz t t'} : [L | t ⤳* t'] -> [L|tNatElim P hs hz t ⤳* tNatElim P hs hz t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_boolElim {L P ht hf t t'} : [ L | t ⤳* t'] -> [L|tBoolElim P ht hf t ⤳* tBoolElim P ht hf t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_emptyElim {L P t t'} : [L | t ⤳* t'] -> [L|tEmptyElim P t ⤳* tEmptyElim P t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_treeElim {L P hl hn t t'} : [L | t ⤳* t'] -> [L|tTreeElim P hl hn t ⤳* tTreeElim P hl hn t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_fst {L t t'} : [ L | t ⤳* t'] -> [L|tFst t ⤳* tFst t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_snd { L t t'} : [ L | t ⤳* t'] -> [L | tSnd t ⤳* tSnd t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_idElim { L A x P hr y t t'} : [ L | t ⤳* t'] -> [L | tIdElim A x P hr y t ⤳* tIdElim A x P hr y t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_alpha {L i t t'} : [L | t ⤳* t'] -> [L | tApp (tAlpha i) t ⤳* tApp (tAlpha i) t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now econstructor.
Qed.

Lemma redalg_alphaSucc {L i t t'} : [L | tApp (tAlpha i) t ⤳* tApp (tAlpha i) t'] ->
  [L | tApp (tAlpha i) (tSucc t) ⤳* tApp (tAlpha i) (tSucc t')].
Proof.
  intros hα.
  change (match tApp (tAlpha i) t, tApp (tAlpha i) t' with
    | tApp (tAlpha i) u, tApp (tAlpha _) u' => [L | tApp (tAlpha i) (tSucc u) ⤳* tApp (tAlpha i) (tSucc u')]
    | _,_ => unit end).
  induction hα; destruct t0; try apply tt; destruct t0_1; try apply tt;
  [reflexivity|]; destruct u; try apply tt; destruct u1; try apply tt.
  inversion o; subst.
  - inversion H2.
  - econstructor; tea; now econstructor.
  - econstructor; tea; now econstructor.
  - destruct b; inversion hα; subst; inversion H.
Qed.

Lemma redalg_alphanSucc {L i t t' n} : [L | tApp (tAlpha i) t ⤳* tApp (tAlpha i) t'] ->
  [L | tApp (tAlpha i) (nSucc n t) ⤳* tApp (tAlpha i) (nSucc n t')].
Proof.
  induction n; intros.
  - tea.
  - eauto using redalg_alphaSucc.
Qed.


Lemma redalg_one_step {L t t'} : [ L | t ⤳ t'] -> [ L | t ⤳* t'].
Proof. intros; econstructor;[tea|reflexivity]. Qed.

Lemma eta_expand_beta { L A t} : [ L | (eta_expand (tLambda A t)) ⤳ t].
Proof.
  cbn.
  evar (t' : term).
  replace t with t' at 2 ; subst t'.
  1: econstructor.
  substify.
  now bsimpl.
Qed.

Lemma eta_expand_beta_inv {L A t t'} :
  [L | tApp (tLambda A t)⟨↑⟩ (tRel 0) ⤳* t'] ->
  whnf t' ->
  [L | t ⤳* t'].
Proof.
  intros red nf.
  inversion red ; subst ; clear red.
  - exfalso.
    inversion nf ; subst ; clear nf.
    inversion H ; subst ; clear H.
    inversion H1 ; subst ; clear H1.
  - inversion H ; subst.
    2: now inversion H4.
    refold.
    replace (_[_]) with t in H0.
    1: now assumption.
    now bsimpl.
Qed.


Lemma eta_expand_fst_inv {L A B t u t'} :
  [L | tFst (tPair A B t u) ⤳* t'] ->
  whnf t' ->
  [L | t ⤳* t'].
Proof.
  intros red nf.
  inversion red ; subst ; clear red.
  - exfalso.
    inversion nf ; subst ; clear nf.
    inversion H ; subst ; clear H.
    inversion H1 ; subst ; clear H1.
  - inversion H ; subst.
    1: now inversion H2.
    eassumption.
Qed.


Lemma eta_expand_snd_inv {L A B t u u'} :
  [L | tSnd (tPair A B t u) ⤳* u'] ->
  whnf u' ->
  [L|u ⤳* u'].
Proof.
  intros red nf.
  inversion red ; subst ; clear red.
  - exfalso.
    inversion nf ; subst ; clear nf.
    inversion H ; subst ; clear H.
    inversion H1 ; subst ; clear H1.
  - inversion H ; subst.
    1: now inversion H2.
    eassumption.
Qed.
(** * LogRel.Syntax.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils AutoSubst.Extra Notations.
From Equations Require Import Equations. (* for depelim *)
From LogRel.Syntax Require Import BasicAst Context NormalForms Weakening Computations.

(** ** Reductions *)

(** *** One-step reduction. *)

Inductive OneRedAlg {L : Fcontext} : term -> term -> Type :=
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
| alphaSubst {n n'} :
  [ L | n ⤳ n' ] -> [ L | tAlpha n ⤳ tAlpha n' ]
| alphaSubstSucc {n n'} :
  [ L | tAlpha n ⤳ tAlpha n' ] -> [ L | tAlpha (tSucc n) ⤳ tAlpha (tSucc n') ]
| alphaRed {n b} : in_Fctx L n b ->
  [ L | tAlpha (nat_to_term n) ⤳ bool_to_term b]
| emptyElimSubst {P e e'} :
    [L |e ⤳ e'] ->
    [L |tEmptyElim P e ⤳ tEmptyElim P e']
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

where "[ L | t ⤳ t' ]" := (@OneRedAlg L t t') : typing_scope.

(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg {L : Fcontext} : term -> term -> Type :=
  | redIdAlg {t} :
    [ L | t ⤳* t ]
  | redSuccAlg {t t' u} :
    [ L | t ⤳ t'] ->
    [ L | t' ⤳* u ] ->
    [ L | t ⤳* u ]
  where "[ L | t ⤳* t' ]" := (@RedClosureAlg L t t') : typing_scope.

Equations Derive Signature for RedClosureAlg.

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
  whne n -> [ L | n ⤳ u] -> False.
Proof.
  intros ne red.
  induction red in ne |- *.
  11: clear i; induction n.
  all : inversion ne; subst; clear ne; try now inv_whne.
  inversion red.
Qed.

Lemma whnf_nored L n u :
  whnf n -> [ L | n ⤳ u] -> False.
Proof.
  intros nf red.
  induction red in nf |- *.
  2,3,6,9,12,13,15,18 : inversion nf; subst; inv_whne; subst; apply IHred; now constructor.
  7:clear i; induction n.
  1-11: inversion nf; subst; inv_whne; subst; try now inv_whne.
  - apply IHred; now constructor.
  - apply IHn; now constructor.
Qed.

(** *** Determinism of reduction *)

Lemma ored_detaux : forall {L n n'}, [ L | tAlpha (nat_to_term n) ⤳ tAlpha n'] -> False.
Proof.
  intros L n.
  induction n; intros.
  - inversion H; subst.
    * inversion H2.
    * destruct b; inversion H1.
  - inversion H; subst.
    * inversion H2.
    * now apply IHn in H2.
    * destruct b; inversion H1.
Qed.

Lemma ored_det {L t u v} :
  [L | t ⤳ u] -> [L | t ⤳ v] ->
  u = v.
Proof.
  intros red red'.
  induction red in v, red' |- *.
  - inversion red' ; subst ; clear red'.
    + reflexivity.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
  - inversion red' ; subst ; clear red'.
    + exfalso.
      eapply whnf_nored.
      2: eassumption.
      now econstructor.
    + f_equal.
      eauto.
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst.
    2,3: exfalso; eapply whnf_nored; tea; constructor.
    f_equal; eauto. 
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; try reflexivity; subst.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst.
    + f_equal; now apply IHred.
    + inversion red.
    + destruct n0; inversion red.
  - inversion red'; subst.
    + inversion H0.
    + apply IHred in H0.
      inversion H0; subst.
      reflexivity.
    + destruct n0; inversion H; subst.
      destruct (ored_detaux red).
  - inversion red'; subst.
    + destruct (ored_detaux red').
    + destruct (ored_detaux red').
    + apply nat_to_term_inj in H.
      destruct H.
      f_equal.
      now eapply functionality.
  - inversion red'; subst.
    f_equal; eauto.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; clear red'.
    1: f_equal; now eapply IHred.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored; tea; constructor.
  - inversion red'; subst; try reflexivity.
    exfalso; eapply whnf_nored;tea; constructor.
  - inversion red'; subst.
    2: f_equal; eauto.
    exfalso; eapply whnf_nored;tea; constructor.
Qed.

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

Lemma oFredalg L L' t u: 
  Fweakening L' L ->
  [L | t ⤳ u] -> [L' | t ⤳ u].
Proof.
  intros hFwk hred.
  induction hred.
  all: now constructor.
Defined.

Lemma cFredalg L L' t u: 
  Fweakening L' L ->
  [L | t ⤳* u] -> [L' | t ⤳* u].
Proof.
  induction 2; econstructor; eauto using oFredalg.
Defined.

Lemma oredalg_wk (ρ : nat -> nat) L (t u : term) :
  [L | t ⤳ u] ->
  [L | t⟨ρ⟩ ⤳ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  2-10,12-18: cbn; asimpl; now econstructor.
  - cbn ; asimpl.
    evar (t' : term).
    replace (subst_term _ t) with t'.
    all: subst t'.
    1: econstructor.
    now asimpl.
  - asimpl. rewrite nat_to_term_ren. rewrite bool_to_term_ren.
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
  intros. apply credalg_wk. destruct ρ. now eapply cFredalg.
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

Lemma redalg_alpha {L t t'} : [L | t ⤳* t'] -> [L | tAlpha t ⤳* tAlpha t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now econstructor.
Qed.

Lemma redalg_alphaSucc {L t t'} : [L | tAlpha t ⤳* tAlpha t'] -> [L | tAlpha (tSucc t) ⤳* tAlpha (tSucc t')].
Proof.
  intros hα.
  change (match tAlpha t, tAlpha t' with
    |tAlpha u, tAlpha u' => [L | tAlpha (tSucc u) ⤳* tAlpha (tSucc u')]
    | _,_ => unit end).
  induction hα; destruct t0; try apply tt; [reflexivity|destruct u]; try apply tt.
  inversion o; subst.
  - econstructor; tea; now econstructor.
  - econstructor; tea; now econstructor.
  - destruct b; inversion hα; subst; inversion H.
Qed.

Lemma redalg_alphanSucc {L t t' n} : [L | tAlpha t ⤳* tAlpha t'] -> [L | tAlpha (nSucc n t) ⤳* tAlpha (nSucc n t')].
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
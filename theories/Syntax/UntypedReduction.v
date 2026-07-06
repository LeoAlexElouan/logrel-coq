(** * LogRel.Syntax.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils AutoSubst.Extra Notations.
From Equations Require Import Equations. (* for depelim *)
From LogRel.Syntax Require Import BasicAst Context NormalForms Weakening Computations.

(** ** Reductions *)

(** *** One-step reduction. *)


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
| evalBox {ℓ ℓ' t} : [ L | tEval ℓ (tBox ℓ' t) ⤳ t]
| xiSubst {ℓ n n' k} : [L | n ⤳ n'] -> [L | tXi ℓ (nSucc k n) ⤳ tXi ℓ (nSucc k n')]
| xiLeaf {ℓ n }: [L | tXi ℓ (nat_to_term n) ⤳ tLeaf (nat_to_term n) ]
| xiNode {ℓ : ell} {n} {k : newnat ℓ} : whne (ellNe k 0) n ->
  [L |tXi ℓ n ⤳ tNode (nat_to_term k) (tXi (cons_ell ℓ k true) n) (tXi (cons_ell ℓ k false) n) ]
| xxiSubst {ℓ m m' n k} : [L | m ⤳ m'] -> [L | tXXi ℓ (nSucc k m) n ⤳ tXXi ℓ (nSucc k m') n]
| xxiLeaf {ℓ k n} : [L | tXXi ℓ (nat_to_term k) n ⤳ tRefl tTree (tLeaf (nat_to_term k)) ]
| xxiNode {ℓ : ell} {m n} {k : newnat ℓ} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) : whne (ellNe k 0) m ->
  [L | tXXi ℓ m n ⤳
    tEllElim k ℓ (tId tNat (dEval (tXi ℓ m)⟨↑⟩ (tEval ℓ (tRel 0))) m)
      (tXXi ℓt m⟨upRen_term_term ↑⟩[tBox ℓ (tEval ℓt (tRel 0))]⇑ (tRel 0))
      (tXXi ℓf m⟨upRen_term_term ↑⟩[(tBox ℓ (tEval ℓf (tRel 0)))]⇑ (tRel 0))
      n (tApp (tEval ℓ n) (nat_to_term k))]
| ellElimSubst {k ℓ P ht hf n b b'}: [L | b ⤳ b'] -> [L | tEllElim k ℓ P ht hf n b ⤳ tEllElim k ℓ P ht hf n b']
| ellElimTrue {ℓ : ell} {k : newnat ℓ} {P ht hf n} :
  [L | tEllElim k ℓ P ht hf n tTrue ⤳ ht[(tBox (cons_ell ℓ k true) (tEval ℓ n))..]]
| ellElimFalse {ℓ : ell} {k : newnat ℓ} {P ht hf n} :
  [L | tEllElim k ℓ P ht hf n tFalse ⤳ ht[(tBox (cons_ell ℓ k false) (tEval ℓ n))..]]

where "[ L | t ⤳ t' ]" := (@OneRedAlg L t t') : typing_scope.



(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg {L : list ell} : term -> term -> Type :=
  | redIdAlg {t} :
    [ L | t ⤳* t ]
  | redSuccAlg {t t' u} :
    [ L | t ⤳ t'] ->
    [ L | t' ⤳* u ] ->
    [ L | t ⤳* u ]
  where
 "[ L | t ⤳* t' ]" := (@RedClosureAlg L t t') : typing_scope.

Equations Derive Signature for OneRedAlg.
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
  match goal with [ H : whne _ _ |- _ ] => inversion H; block H end.


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

Lemma whne_nored {L} n u nevar:
  whne nevar n -> [ L | n ⤳ u] -> False.
Proof.
  intros ne red.
  induction ne in u, red |-*.
  1-14: inversion red; subst; clear red; nSucc_handler.
  all: try solve [now inversion ne | now inversion H2].
  * destruct (notin_is_not_in ltac:(tea) ltac:(tea)).
  * destruct k.
    2: inversion H2.
    pose proof (nevar_uniq ne H2).
    destruct nevar; inversion H.
  * inversion H3.
  * destruct k.
    2: inversion H3.
    pose proof (nevar_uniq ne H3).
    destruct nevar; inversion H.
Qed.

Ltac inv_alpha :=
  match goal with
    [ H : [_ | tAlpha _ ⤳ _] |- _ ] => inversion H
    | [ H : whne (tAlpha _) |- _ ] => inversion H end.
Lemma whnf_nored L n u :
  @whnf n -> [ L | n ⤳ u] -> False.
Proof.
  intros nf red.
  induction nf.
  all: try now inversion red.
  now eapply whne_nored.
Qed.

(** *** Determinism of reduction *)

(* Lemma ored_detaux : forall {L i i' n n'}, [ L | tApp (tAlpha i) (nat_to_term n) ⤳ tApp (tAlpha i') n'] -> False.
Proof.
  intros L i i' n n' H.
  inversion H; subst; clear H.
  * inversion X.
  * eapply eq_sym, nSucc_nat_to_term in H2 as [[] <-].
    - inversion X.
    - inversion X.
  * destruct b; inversion H3.
Qed. *)


Lemma ored_det {L t u v} :
  [L | t ⤳ u] -> [L | t ⤳ v] -> u = v.
Proof.
  intros red red'.
  induction red in v, red' |-*.
  all: depelim red'; nSucc_handler; eauto.
(*   1-29: inversion red'; subst; clear red'; nSucc_handler; eauto. *)
(*   71-72 : depelim red'. *)
  all : try solve [repeat f_equal; eauto].
  all : repeat match goal with r : [_ | _ ⤳ _] |- _ => try solve [inversion r]; block r | _ => idtac end; unblock.
  all : try match goal with w : whne _ (nSucc ?k _) |- _ => destruct k; [ | inversion w]; cbn in w end .
  all : try match goal with w : whne _ (nat_to_term ?k) |- _ => destruct k; inversion w end .
  all: try solve [exfalso; eapply whne_nored; eauto].
  * eapply index_to_nat_inj in H as <-.
    eapply f_equal, functionality; tea.
  * eapply f_equal, functionality; tea.
  * pose proof (nevar_uniq w w0).
    destruct k as [k wf], k0 as [k0 wf0]; cbn in *.
    now inversion H; subst.
  * pose proof (nevar_uniq w w0).
    destruct k as [k wf], k0 as [k0 wf0]; cbn in *.
    now inversion H; subst.
  * destruct k as [k wf], k0 as [k0 wf0]; cbn in *.
    now inversion H; subst.
  * destruct k as [k wf], k0 as [k0 wf0]; cbn in *.
    now inversion H; subst.
Qed.

Lemma red_whne {L} t u nevar : [ L | t ⤳* u] -> whne nevar t -> t = u.
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
  eapply well_Fwk_in; tea.
Defined.

Lemma oredalg_wk (ρ : nat -> nat) L (t u : term) :
  [L | t ⤳ u] ->
  [L | t⟨ρ⟩ ⤳ u⟨ρ⟩].
Proof.
  intros Hred.
  induction Hred in ρ |- *.
  all: cbn.
  all: rewrite ? nSucc_ren, ? subst_ren_up,
    ? nat_to_term_ren, ? bool_to_term_ren.
  all: try now econstructor.
  - econstructor.
    exact (whne_ren _ _ _ w).
  - cbn. simpl. repeat (unfold funcomp; cbn).
    replace m⟨upRen_term_term ↑⟩⟨upRen_term_term (upRen_term_term ρ)⟩
      with m⟨upRen_term_term ρ⟩⟨upRen_term_term ↑⟩.
    replace m⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩⟨upRen_term_term (upRen_term_term (upRen_term_term ρ))⟩
      with m⟨upRen_term_term ρ⟩⟨upRen_term_term ↑⟩⟨upRen_term_term ↑⟩.
    refine (xxiNode _).
    { exact (whne_ren _ _ _ w). }
    all: now bsimpl.
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

Lemma cFredalg L L' (wρε : well_Fweakening L' L) t u: 
  [L | t ⤳* u] -> [L' | t ⤳* u].
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

(* Lemma redalg_alpha {L i t t'} : [L | t ⤳* t'] -> [L | tApp (tAlpha i) t ⤳* tApp (tAlpha i) t'].
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
 *)

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
    repeat inv_whne.
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
    repeat inv_whne.
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
    repeat inv_whne.
  - inversion H ; subst.
    1: now inversion H2.
    eassumption.
Qed.
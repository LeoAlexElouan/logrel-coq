(** * LogRel.Syntax.Weakening: definition of well-formed weakenings, and some properties. *)
From Stdlib Require Import Lia ssrbool.
From Equations Require Import Equations.
From LogRel Require Import Utils AutoSubst.Extra Notations.
From LogRel.Syntax Require Import BasicAst Context NormalForms.

(** ** Raw weakenings *)

(** Weakenings are an intentional representation of a subclass of renamings
(order-preserving ones), to allow easy proofs by induction. There is a unique
representation for extensionally equal renamings. *)

Inductive weakening : Set :=
  | _wk_empty : weakening
  | _wk_step (w : weakening) : weakening
  | _wk_up (w : weakening) : weakening.
  
Equations Derive NoConfusion EqDec for weakening.

Fixpoint _wk_id (Γ : Tcontext) : weakening :=
  match Γ with
    | nil => _wk_empty
    | cons _ Γ' => _wk_up (_wk_id Γ')
  end.

(** Transforms an (intentional) weakening into a renaming. *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | _wk_empty => id
    | _wk_step ρ' => (wk_to_ren ρ') >> S
    | _wk_up ρ' => up_ren (wk_to_ren ρ')
  end.

Lemma wk_to_ren_id Γ : (wk_to_ren (_wk_id Γ)) =1 id.
Proof.
  induction Γ.
  1: reflexivity.
  intros [] ; cbn.
  2: rewrite IHΓ.
  all: reflexivity.
Qed.

Coercion wk_to_ren : weakening >-> Funclass.


(** ** Instance: how to rename by a well-formed weakening. *)

#[global] Instance Ren1_wk {Y Z : Type} `(ren : Ren1 (nat -> nat) Y Z) :
(Ren1 weakening Y Z) := fun ρ t => t⟨wk_to_ren ρ⟩.

Arguments Ren1_wk {_ _ _} _ _/.

Fixpoint wk_compose (ρ ρ' : weakening) : weakening :=
  match ρ, ρ' with
    | _wk_empty , _ => ρ'
    | _wk_step ν , _ => _wk_step (wk_compose ν ρ')
    | _wk_up ν, _wk_empty => ρ
    | _wk_up ν, _wk_step ν' => _wk_step (wk_compose ν ν')
    | _wk_up ν, _wk_up ν' => _wk_up (wk_compose ν ν')
  end.

Lemma wk_compose_compose (ρ ρ' : weakening) : wk_to_ren (wk_compose ρ ρ') =1 ρ' >> ρ.
Proof.
  induction ρ in ρ' |- *.
  - reflexivity.
  - cbn.
    rewrite IHρ.
    now fsimpl.
  - destruct ρ'.
    + reflexivity.
    + cbn.
      rewrite IHρ.
      now asimpl.
    + cbn.
      asimpl.
      rewrite IHρ.
      now asimpl.
Qed.

(** ** Well-formed weakenings between two contexts *)

(** To avoid dependency issues, we define well-formed weakenings as
a predicate on raw weakenings defined above, rather than directly
using indexed weakenings. *)

Inductive well_weakening : weakening -> Tcontext -> Tcontext -> Type :=
  | well_empty : well_weakening _wk_empty nil nil
  | well_step {Γ Δ : Tcontext} (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_step ρ) (cons A Γ) Δ
  | well_up {Γ Δ : Tcontext} (A : term) (ρ : weakening) :
    well_weakening ρ Γ Δ -> well_weakening (_wk_up ρ) (cons A⟨ρ⟩ Γ) (cons A Δ).

Derive Signature for well_weakening.

Lemma well_wk_irr : forall ρ Γ Δ (w1 w2 : well_weakening ρ Γ Δ), w1 = w2.
Proof.
induction w1.
+ now depelim w2.
+ now depelim w2; now f_equal.
+ depelim w2.
  replace e' with (@eq_refl _ (A⟨ρ⟩)) in H by apply eqdec_uip, term_EqDec.
  cbn in H; rewrite H; now f_equal.
Qed.

Lemma well_wk_id (Γ : Tcontext) : well_weakening (_wk_id Γ) Γ Γ.
Proof.
  induction Γ as [|d].
  1: econstructor.
  replace d with (d⟨wk_to_ren (_wk_id Γ)⟩) at 2.
  1: now econstructor.
  cbn.
  f_equal.
  rewrite wk_to_ren_id.
  now asimpl.
Qed.

Lemma well_wk_compose {ρ ρ' : weakening} {Δ Δ' Δ'' : Tcontext} :
  well_weakening ρ Δ Δ' -> well_weakening ρ' Δ' Δ'' -> well_weakening (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - eassumption.
  - econstructor. auto.
  - inversion H' as [| | ? ? A' ν']; subst ; clear H'.
    1: now econstructor ; auto.
    asimpl ; refold.
    erewrite extRen_term ; refold.
    2: symmetry ; now apply wk_compose_compose.
    econstructor ; auto.
Qed.

Class Fweakening (L L' : Fcontext) : SProp := ρF : forall n b, in_Fctx L' n b -> in_Fctx L n b.
Notation "L ≤ε L'" := (Fweakening L L').

#[projections(primitive)]Record wk_well_wk {Γ Δ : context} :=
  { wk :> weakening ; well_wk :> well_weakening wk (Tctx Γ) (Tctx Δ); Fwk :> Fweakening Γ Δ}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).


Lemma wk_well_wk_wk_eq : forall Γ Δ (ρ1 ρ2 : Γ ≤ Δ),
  ρ1.(wk) = ρ2.(wk) -> ρ1 = ρ2.
Proof.
intros Γ Δ [ρ1 w1] [ρ2 w2]; cbn; intros <-.
assert (e : w1 = w2) by apply well_wk_irr; now destruct e.
Qed.

#[global] Hint Resolve well_wk : core.

(** ** Instance: how to rename by a well-formed weakening. *)

#[global] Instance Ren1_well_wk {Y Z : Type} `{Ren1 (nat -> nat) Y Z} {Γ Δ : context} :
  (Ren1 (Γ ≤ Δ) Y Z) :=
  fun ρ t => t⟨wk_to_ren ρ⟩. (* fun ρ t => t⟨wk_to_ren ρ.(wk)⟩. *)

Arguments Ren1_well_wk {_ _ _ _ _} _ _/.

Ltac fold_wk_ren :=
  change (@ren1 _ _ _ Ren_term (wk_to_ren (@wk _ _ ?ρ)))
    with (@ren1 _ _ _ (@Ren1_well_wk _ _ _ _ _) ρ);
  change (@ren1 _ _ _ (@Ren1_wk _ _ _) (@wk _ _ ?ρ))
    with (@ren1 _ _ _ (@Ren1_well_wk _ _ _ _ _) ρ).

Smpl Add 20 fold_wk_ren : refold.

Ltac change_well_wk :=
    change ren_term with (@ren1 _ _ _ Ren1_well_wk) in *.

Smpl Add 10 change_well_wk : refold.

#[global] Hint Immediate Fwk : typeclass_instances.

(** Constructors of well-typed weakenings *)
Definition Fwk_empty : ε ≤ε ε := fun n b hin => hin.
Definition wk_empty : (ε ≤ ε) :=
  Build_wk_well_wk ε ε _wk_empty well_empty Fwk_empty.


Definition _Fwk_step {Γ Δ : context} {A}: Γ ≤ε Δ -> (Γ,,A) ≤ε Δ := fun ρ n b hin => (ρ n b hin). (* For symmetry. Fwk_id should always work *)
Definition wk_step {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,A) ≤ Δ :=
  Build_wk_well_wk (Γ,,A) Δ (_wk_step ρ) (well_step A ρ ρ) (_Fwk_step ρ).

Definition Fwk_up {Γ Δ A} (ρ : Γ ≤ Δ): (Γ,, A⟨ρ⟩) ≤ε Δ -> (Γ,,A) ≤ε Δ := fun ρ n b hin => (ρ n b hin).
Definition wk_up {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,  A⟨ρ⟩) ≤ (Δ ,, A) :=
  Build_wk_well_wk (Γ,,  A⟨ρ⟩) (Δ ,, A) (_wk_up ρ) (well_up A ρ ρ) (Fwk_up ρ ρ).

Definition Fwk_id {Γ} : Γ ≤ε Γ := fun n b hin => hin.
Definition wk_id {Γ} : Γ ≤ Γ :=
  Build_wk_well_wk Γ Γ (_wk_id (Tctx Γ)) (well_wk_id (Tctx Γ)) Fwk_id.

Definition wk_Fwk {Γ: context} {L} (ρF : L ≤ε Γ) : (Build_context Γ L) ≤ Γ :=
  Build_wk_well_wk (Build_context Γ L) _ (_wk_id Γ) (well_wk_id Γ) ρF.

Definition Fwk_compose {Γ Γ' Γ''} : Γ ≤ε Γ' -> Γ' ≤ε Γ'' -> Γ ≤ε Γ'' := fun ρ ρ' n b hin => ρ n b (ρ' n b hin).
Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' :=
  Build_wk_well_wk Γ Γ'' (wk_compose ρ.(wk) ρ'.(wk)) (well_wk_compose ρ.(well_wk) ρ'.(well_wk)) (Fwk_compose ρ ρ').
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').

(** ** The ubiquitous operation of adding one variable at the end of a context *)

Definition wk1 {Γ} A : Γ,, A ≤ Γ := wk_step A (wk_id (Γ := Γ)).

Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Tctx Δ| <= #|Tctx Γ|.
Proof.
  destruct ρ as [ρ wellρ].
  induction wellρ.
  all: cbn ; lia.
Qed.


Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : ρ.(wk) = (_wk_id (Tctx Γ)).
Proof.
  destruct ρ as [ρ wellρ] ; cbn.
  pose proof (@eq_refl _ #|Tctx Γ|) as eΓ.
  revert eΓ wellρ.
  generalize Γ at 2 4.
  intros Δ e wellρ.
  induction wellρ in e |- *.
  all: cbn.
  - reflexivity.
  - set (Γ' := (Build_context Γ0 (Fctx Γ))).
    set (Δ' := (Build_context Δ0 (Fctx Γ))).
    pose proof (well_length (Build_wk_well_wk Γ' Δ' ρ wellρ Fwk0)).
    now cbn in * ; lia.
  - rewrite IHwellρ.
    2: now cbn in * ; lia.
    reflexivity.
Qed.

Lemma wk1_ren {Γ A} : @wk1 Γ A =1 ↑.
Proof.
  intros ? ; cbv -[wk_to_ren _wk_id]. cbn.
  now rewrite wk_to_ren_id.
Qed.

Lemma wk_up_ren {Γ Δ A} (ρ : Δ ≤ Γ) :
  wk_up A ρ =1 upRen_term_term ρ.
Proof.
  intros; cbn; now asimpl.
Qed.

Section RenWlWhnf.

  Context {Γ Δ} (ρ : Δ ≤ Γ).

  Lemma whne_ren_wl t : whne t -> whne (t⟨ρ⟩).
  Proof.
    apply whne_ren.
  Qed.

  Lemma whnf_ren_wl t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    apply whnf_ren.
  Qed.

  Lemma isType_ren_wl A : isType A -> isType (A⟨ρ⟩).
  Proof.
    apply isType_ren.
  Qed.

  Lemma isPosType_ren_wl A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    apply isPosType_ren.
  Qed.

  Lemma isFun_ren_wl f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    apply isFun_ren.
  Qed.

  Lemma isPair_ren_wl f : isPair f -> isPair (f⟨ρ⟩).
  Proof.
    apply isPair_ren.
  Qed.

  Lemma isCanonical_ren_wl t : isCanonical t <~> isCanonical (t⟨ρ⟩).
  Proof.
    symmetry.
    apply isCanonical_ren.
  Qed.

End RenWlWhnf.

#[global] Hint Resolve whne_ren_wl whnf_ren_wl isType_ren_wl isPosType_ren_wl isFun_ren_wl isCanonical_ren_wl : gen_typing.

(** ** Adaptation of AutoSubst's asimpl to well typed weakenings *)

Ltac bsimpl' :=
  repeat (first
    [ progress setoid_rewrite substSubst_term_pointwise
    | progress setoid_rewrite substSubst_term
    | progress setoid_rewrite substRen_term_pointwise
    | progress setoid_rewrite substRen_term
    | progress setoid_rewrite renSubst_term_pointwise
    | progress setoid_rewrite renSubst_term
    | progress setoid_rewrite renRen'_term_pointwise
    | progress setoid_rewrite renRen_term
    | progress setoid_rewrite varLRen'_term_pointwise
    | progress setoid_rewrite varLRen'_term
    | progress setoid_rewrite varL'_term_pointwise
    | progress setoid_rewrite varL'_term
    | progress setoid_rewrite rinstId'_term_pointwise
    | progress setoid_rewrite rinstId'_term
    | progress setoid_rewrite instId'_term_pointwise
    | progress setoid_rewrite instId'_term
    | progress setoid_rewrite wk_to_ren_id
    | progress setoid_rewrite wk_compose_compose
    | progress setoid_rewrite id_ren
    | progress setoid_rewrite wk1_ren
    | progress setoid_rewrite scons_eta' (** missing from AutoSubst's database? *)
    | progress unfold
        up_term_term, upRen_term_term, up_ren, wk_well_wk_compose,
        wk_id, wk_step, wk_up, wk_empty (**, _wk_up, _wk_step *)
    | progress cbn[subst_term ren_term wk wk_to_ren]
    | progress fsimpl ]).

Ltac bsimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Ren1_subst, Ren1_wk, Ren1_well_wk
                  in *; bsimpl'; minimize.

(** ** Weakenings play well with context access *)

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Γ n decl ->
in_ctx Δ (ρ n) (decl⟨ρ⟩).
Proof.
  intros Hdecl.
  destruct ρ as [ρ wfρ Fρ]; (* destruct Γ as [Γ L], Δ as [Δ L'] ; unfold in_ctx; *) cbn in *.
  change Γ with (Build_context Γ Γ) in Hdecl; change Δ with (Build_context Δ Δ). unfold in_ctx, ren1 in *; cbn in *.
  induction wfρ in n, decl, Hdecl |- *.
  - inversion Hdecl.
  - cbn.
    replace (decl⟨_⟩) with (decl⟨ρ⟩⟨↑⟩) by now asimpl.
    now econstructor.
  - destruct n ; cbn.
    + inversion Hdecl ; subst ; clear Hdecl.
      replace (A⟨↑⟩⟨_⟩) with (A⟨ρ⟩⟨↑⟩) by now asimpl.
      now constructor.
    + inversion Hdecl ; subst ; cbn in * ; refold.
      replace (A0⟨_⟩⟨_⟩) with (A0⟨ρ⟩⟨↑⟩) by now asimpl.
      now econstructor.
Qed.

Lemma in_ctx_str (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Δ (ρ n) decl ->
∑ decl', decl = decl'⟨ρ⟩ × in_ctx Γ n decl'.
Proof.
intros Hdecl.
destruct ρ as [ρ wfρ] ; destruct Γ, Δ; unfold in_ctx; cbn in *.
induction wfρ in n, decl, Hdecl |- *.
- inversion Hdecl.
- cbn in *.
inversion Hdecl ; subst.
edestruct IHwfρ as [? []]; tea ; subst.
eexists ; split ; tea.
now bsimpl.
- destruct n ; cbn in *.
+ inversion Hdecl ; subst ; clear Hdecl.
  eexists ; split.
  2: now constructor.
  now bsimpl.
+ inversion Hdecl ; subst ; clear Hdecl ; cbn in *.
  edestruct IHwfρ as [? []]; tea ; subst.
  eexists ; split.
  2: now econstructor.
  now bsimpl.
Qed.

(** Lemmas for easier rewriting *)

(** Note: should be unnecessary since scons_eta' is in bsimpl now… *)
Lemma upren_subst_rel0 t : t[(tRel 0)]⇑ = t.
Proof. now bsimpl. Qed.

Lemma subst_ren_wk {Γ Δ A σ} (ρ : Δ ≤ Γ) : A[σ]⟨ρ⟩ = A[σ⟨ρ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_upren t σ ρ : t[up_term_term σ]⟨upRen_term_term ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. asimpl; unfold Ren1_subst; asimpl; substify; now asimpl. Qed.

Lemma eq_upren' {Γ Δ} A t σ (ρ : Δ ≤ Γ) : t[up_term_term σ]⟨wk_up A ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. eapply eq_upren. Qed.

Lemma subst_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof. now bsimpl. Qed.

Lemma subst1_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ) : P[n .: ρ >> tRel] = P⟨wk_up A ρ⟩[n..].
Proof. now bsimpl. Qed.

Lemma subst_ren_wk_up2 {Γ Δ P A B a b} (ρ : Γ ≤ Δ):
  P[a .: b..]⟨ρ⟩ = P⟨wk_up A (wk_up B ρ)⟩[a⟨ρ⟩ .: b⟨ρ⟩..].
Proof. now bsimpl. Qed.

Lemma subst_ren_subst_mixed {Γ Δ P n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P[n⟨ρ⟩ .: ρ >> tRel].
Proof. now bsimpl. Qed.

Lemma subst_ren_subst_mixed2 {Γ Δ P a b} (ρ : Γ ≤ Δ): P[a .: b..]⟨ρ⟩ = P[a⟨ρ⟩ .: (b⟨ρ⟩ .: ρ >> tRel)].
Proof. now bsimpl. Qed.

Lemma subst_ren_subst_mixed3 {Γ Δ Ξ P n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) :
  P[n⟨ρ⟩ .: ρ ∘w ρ' >> tRel] = P[n .: ρ' >> tRel]⟨ρ⟩.
Proof. now bsimpl. Qed.


Lemma wk_up_ren_subst {Γ Δ Ξ P A n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) :
  P[n .: ρ ∘w ρ' >> tRel] = P⟨wk_up A ρ'⟩[n .: ρ >> tRel].
Proof. now bsimpl. Qed.

Lemma shift_subst_scons {B a Γ Δ} (ρ : Δ ≤ Γ) : B⟨↑⟩[a .: ρ >> tRel] = B⟨ρ⟩.
Proof. bsimpl; now rewrite rinstInst'_term. Qed.

Lemma shift_subst1 {B a} : B⟨↑⟩[a..] = B.
Proof. now bsimpl. Qed.

Lemma shift_upRen ρ t : t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨upRen_term_term ρ⟩.
Proof. now asimpl. Qed.

Lemma wk_comp_ren_on {Γ Δ Ξ} (H : term) (ρ1 : Γ ≤ Δ) (ρ2 : Δ ≤ Ξ) :
  H⟨ρ2⟩⟨ρ1⟩ = H⟨ρ1 ∘w ρ2⟩.
Proof. now bsimpl. Qed.

Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. now bsimpl. Qed.

Lemma wk1_ren_on Γ F (H : term) : H⟨@wk1 Γ F⟩ = H⟨↑⟩.
Proof. now bsimpl. Qed.

Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) F (H : term) : H⟨wk_up F ρ⟩ = H⟨upRen_term_term ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_up_wk1_ren_on Γ F G (H : term) : H⟨wk_up F (@wk1 Γ G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. now bsimpl. Qed.

Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_prod {A B Γ Δ} (ρ : Δ ≤ Γ) : tProd A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tProd A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_lam {A t Γ Δ} (ρ : Δ ≤ Γ) : tLambda A⟨ρ⟩ t⟨wk_up A ρ⟩ = (tLambda A t)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_app {t u Γ Δ} (ρ : Δ ≤ Γ) : tApp t⟨ρ⟩ u⟨ρ⟩ = (tApp t u)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_sig {A B Γ Δ} (ρ : Δ ≤ Γ) : tSig A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tSig A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_pair {A B a b Γ Δ} (ρ : Δ ≤ Γ) : tPair A⟨ρ⟩ B⟨wk_up A ρ⟩ a⟨ρ⟩ b⟨ρ⟩ = (tPair A B a b)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_fst {p Γ Δ} (ρ : Δ ≤ Γ) : tFst p⟨ρ⟩ = (tFst p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_snd {p Γ Δ} (ρ : Δ ≤ Γ) : tSnd p⟨ρ⟩ = (tSnd p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_comp {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp A f g)⟨ρ⟩ = comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_emptyElim {Γ Δ P n} (ρ : Δ ≤ Γ) :
  tEmptyElim P⟨wk_up tEmpty ρ⟩ n⟨ρ⟩ = (tEmptyElim P n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; now bsimpl.
Qed.

Lemma wk_natElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tNatElim P⟨wk_up tNat ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tNatElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_boolElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tBoolElim P⟨wk_up tBool ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tBoolElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_Id {A x y Γ Δ} (ρ : Δ ≤ Γ) : tId A⟨ρ⟩ x⟨ρ⟩ y⟨ρ⟩ = (tId A x y)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_refl {A x Γ Δ} (ρ : Δ ≤ Γ) : tRefl A⟨ρ⟩ x⟨ρ⟩ = (tRefl A x)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_idElim {A x P hr y e Δ Γ} (ρ : Δ ≤ Γ) :
  tIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨wk_up (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) (wk_up A ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩ = (tIdElim A x P hr y e)⟨ρ⟩.
Proof. reflexivity. Qed.


Lemma wk_step_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟩ = t⟨wk_step A ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk_up_wk1 {A t Γ Δ} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟨ρ⟩⟩ = t⟨@wk1 Γ A⟩⟨wk_up A ρ⟩.
Proof. now bsimpl. Qed.



Lemma wk_to_ren_inj : forall Γ Δ (ρ1 ρ2 : Γ ≤ Δ), wk_to_ren ρ1 =1 wk_to_ren ρ2 -> ρ1 = ρ2.
Proof.
  intros * Heq; apply wk_well_wk_wk_eq.
  destruct ρ1 as [ρ1 wρ1 Fρ1], ρ2 as [ρ2 wρ2 Fρ2]; cbn in *. clear Fρ1 Fρ2.
  revert Γ Δ wρ1 ρ2 wρ2 Heq.
  induction ρ1; intros Γ Δ wρ1 ρ2 wρ2 Heq; cbn in *.
  + destruct ρ2; cbn in *; first [reflexivity|exfalso].
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ,Δ; cbn in *.
      depelim wρ1; depelim wρ2.
  + destruct ρ2; cbn in *; first [apply f_equal|exfalso].
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wρ1; depelim wρ2.
      eapply (IHρ1 (Build_context Γ0 L) (Build_context Γ' L') wρ1 _ wρ2).
      intros n; specialize (Heq n).
      now injection Heq.
    - specialize (Heq 0); discriminate Heq.
  + destruct ρ2; cbn in *; first [apply f_equal|exfalso].
    - destruct Γ,Δ; cbn in *.
      depelim wρ1; depelim wρ2.
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wρ1; depelim wρ2.
      eapply (IHρ1 (Build_context Γ0 L) (Build_context Δ L') wρ1 _ wρ2); tea.
      intros n; specialize (Heq (S n)); cbn in Heq.
      now injection Heq.
Qed.



Lemma wk_comp_lunit {Γ Δ} (ρ : Δ ≤ Γ) : wk_id ∘w ρ = ρ.
Proof.
apply wk_to_ren_inj; now bsimpl.
Qed.

Lemma wk_comp_runit {Γ Δ} (ρ : Δ ≤ Γ) : ρ ∘w wk_id = ρ.
Proof.
apply wk_to_ren_inj; now bsimpl.
Qed.



Lemma wk_comp_assoc {Γ Δ Ξ ζ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) (ρ'' : ζ ≤ Ξ) :
  (ρ'' ∘w ρ') ∘w ρ = ρ'' ∘w (ρ' ∘w ρ).
Proof.
apply wk_to_ren_inj; now bsimpl.
Qed.

Lemma wk1_irr {Γ Γ' A A' t} : t⟨@wk1 Γ A⟩ = t⟨@wk1 Γ' A'⟩.
Proof. intros; now rewrite 2!wk1_ren_on. Qed.

Lemma var0_wk1_id {Γ A t} : t[tRel 0 .: @wk1 Γ A >> tRel] = t.
Proof. now bsimpl. Qed.

Lemma eq_subst_scons {Γ} a B : B[a..] = B[a⟨@wk_id Γ⟩ .: @wk_id Γ >> tRel].
Proof. now bsimpl. Qed.

Lemma wk1_subst A Γ F σ : (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ].
Proof. asimpl; now rewrite wk1_ren. Qed.

Lemma ren_subst  {Γ Δ} A (ρ : Γ ≤ Δ) σ : A⟨ρ⟩[σ] = A[ ρ >> σ].
Proof. now asimpl. Qed.

Lemma liftSubstComm Γ F G t σ : G[t]⇑[σ] = G[t[σ] .: @wk1 Γ F >> σ].
Proof. now bsimpl. Qed.


Lemma Fwk_new {L L' : Fcontext} (new : newnat L) b :  L' ≤ε L -> in_Fctx L' new b ->  L' ≤ε (Fcons' L new b).
Proof.
  intros Fρ hin n' b' hin'.
  destruct new; cbn in *.
  inversion hin'; subst.
  - apply hin.
  - now apply Fρ.
Defined.

Lemma wk_new : forall {Γ Δ: context} (new : newnat Γ) b, Δ ≤ Γ -> in_Fctx Δ new b -> Δ ≤ (Γ,, new ↦ b).
Proof.
  intros Γ Δ new b ρ hin.
  apply (Build_wk_well_wk _ _ (wk ρ)).
  apply (well_wk ρ).
  eapply Fwk_new; [apply ρ | apply hin].
Defined.

Lemma Fwk_Fup : forall {L L'} b (Fρ :  L' ≤ε L) (new : newnat L) (new' : newnat L'),
   new = new' :> nat -> (Fcons' L' new' b) ≤ε (Fcons' L new b).
Proof.
  intros * ρε [n hnotin] [n' hnotin'] e n'' b'' hin'.
  cbn in *; destruct e.
  inversion hin'; subst; constructor.
  now apply ρε.
Defined.

Lemma wk_Fup : forall {Γ Δ} b (ρ : Δ ≤ Γ ) (new : newnat Γ) (new' : newnat Δ),
  new = new' :> nat -> (Δ,, new' ↦ b) ≤ (Γ,, new ↦ b).
Proof.
  intros * ρ new new' e.
  apply (Build_wk_well_wk _ _ (wk ρ)).
  apply (well_wk ρ).
  eapply Fwk_Fup.
  apply ρ.
  apply e.
Defined.

(* 
Lemma Fwk_Fup : forall {L L'} b n (Fρ :  L' ≤ε L) (newL : not_in_Fctx L n) (newL' : not_in_Fctx L' n),
   (Fcons' L' (Build_newnat _ n newL') b) ≤ε (Fcons' L (Build_newnat _ n newL) b).
Proof.
  intros L L' b n Fρ newL newL' n' b' hin'.
  inversion hin'; subst; constructor.
  now apply Fρ.
Defined.

Lemma wk_Fup : forall {Γ Δ} b n (ρ : Δ ≤ Γ ) (newΓ : not_in_Fctx Γ n) (newΔ : not_in_Fctx Δ n),
  (Δ,, (Build_newnat _ n newΔ) ↦ b) ≤ (Γ,, (Build_newnat _ n newΓ)↦ b).
Proof.
  intros Γ Δ b n ρ newΓ newΔ.
  apply (Build_wk_well_wk _ _ (wk ρ)).
  apply (well_wk ρ).
  eapply Fwk_Fup.
  apply ρ.
Defined. *)

Definition Fwk_Fstep {L L':Fcontext} (new : newnat L') b :  L' ≤ε L ->  (Fcons' L' new b) ≤ε L:=
  fun Fρ n b hin => in_thereF _ _ _ _ _ (Fρ _ _ hin).

Definition wk_Fstep {Γ Δ} new b (ρ : Γ ≤ Δ) : (Γ,,new ↦ b) ≤ Δ :=
  Build_wk_well_wk (Γ,,new ↦ b) Δ ρ ρ (Fwk_Fstep _ _ ρ).

Definition wk_Fstep_ren_on {Γ Δ} new b (ρ : Γ ≤ Δ) t: t⟨wk_Fstep new b ρ⟩ = t⟨ρ⟩.
Proof.
  reflexivity.
Qed.

Lemma wk_new_notin {L L':Fcontext} (new : newnat L') : L' ≤ε L -> not_in_Fctx L new.
Proof.
  intros ρε.
  eapply not_in_is_notin.
  intros b hin.
  eapply notin_is_not_in, ρε, hin.
  eapply new.
Qed.



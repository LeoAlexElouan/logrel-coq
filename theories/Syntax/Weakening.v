(** * LogRel.Syntax.Weakening: definition of well-formed weakenings, and some properties. *)
From Stdlib Require Import Lia ssrbool.
From Equations Require Import Equations.
From LogRel Require Import Utils AutoSubst.Extra Notations.
From LogRel.Syntax Require Import BasicAst Context NormalForms Computations.

(** ** Raw weakenings *)

(** Weakenings are an intentional representation of a subclass of renamings
(order-preserving ones), to allow easy proofs by induction. There is a unique
representation for extensionally equal renamings. *)

Inductive weakening : Set :=
  | _wk_empty : weakening
  | _wk_step (w : weakening) : weakening
  | _wk_up (w : weakening) : weakening.
  
Equations Derive NoConfusion EqDec for weakening.

Fixpoint _wk_id {A} (Γ : list A) : weakening :=
  match Γ with
    | nil => _wk_empty
    | cons _ Γ' => _wk_up (_wk_id Γ')
  end.

(** Transforms an (intentional) weakening into a renaming. *)
Fixpoint wk_to_ren (ρ : weakening) : nat -> nat :=
  match ρ with
    | _wk_empty => id
    | _wk_step ρ' => (wk_to_ren ρ') >> S
    | _wk_up ρ' => upRen_term_term (wk_to_ren ρ')
  end.

Lemma wk_to_ren_id' {A} (L : list A) : (wk_to_ren (_wk_id L)) =1 id.
Proof.
  induction L.
  1: reflexivity.
  intros [] ; cbn.
  2: rewrite IHL.
  all: reflexivity.
Qed.

Lemma wk_to_ren_id (Γ : Tcontext) : (wk_to_ren (_wk_id Γ)) =1 id.
Proof.
  exact (wk_to_ren_id' _).
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


Definition Fweakening := weakening.

Class Fweakening' (L L' : Fcontext) : SProp := ρF : forall n b, in_Fctx L' n b -> in_Fctx L n b.
Notation "L ≤ε L'" := (Fweakening' L L').

(* #[global] Instance Ren1_Alpha :
  (Ren1 Fweakening term term) :=
  fun ρε t => ren_alpha (wk_to_ren ρε) t. *)

Inductive well_Fweakening : Fweakening -> list Fcontext -> list Fcontext -> Type:=
  | well_emptyF : well_Fweakening _wk_empty nil nil
  | well_stepF {L L'} (F : Fcontext) ρ :
      well_Fweakening ρ L L' -> well_Fweakening (_wk_step ρ) (cons F L) L'
  | well_upF {L L'} (F F': Fcontext) ρ :
      well_Fweakening ρ L L' -> F ≤ε F' -> well_Fweakening (_wk_up ρ) (cons F L) (cons F' L').

Derive Signature for well_Fweakening.

Lemma well_Fwk_irr : forall {ρ L L'} (w1 w2 : well_Fweakening ρ L L'), w1 = w2.
Proof.
  intros ρ L L' w1 w2.
  induction w1.
  - now depelim w2.
  - depelim w2; now f_equal.
  - depelim w2.
    now specialize (IHw1 w2) as [].
Qed.

Lemma well_Fwk_eqdec {ρ L L'} : EqDec (well_Fweakening ρ L L').
Proof. left. eapply well_Fwk_irr. Qed.
Local Existing Instance well_Fwk_eqdec.


Fixpoint ren_index {L L' ρε} (wρε : well_Fweakening ρε L L')
  {struct wρε} : list_index L' -> list_index L :=
    match wρε in well_Fweakening ρε Lw Lw' return list_index Lw' -> list_index Lw with
    | well_emptyF => fun i =>
        match i in list_index Li return (match Li with nil => list_index nil | cons _ _ => unit end) with
        index_0 _ _ | index_S _ _ _=> tt end
    | well_stepF F ρ wρ => fun i => index_S _ _ (ren_index wρ i)
    | well_upF F F' ρ wρ wF => fun i => 
        (match i in list_index Li return
          (match Li with nil => unit |
            cons Fi Li' => (list_index Li' -> list_index _) -> list_index (cons F _) end) with
        | index_0 h t => fun w => index_0 _ _
        | index_S _ _ i' => fun IH => index_S _ _ (IH i')  end) (ren_index wρ)
    end.
Lemma ren_index_to_ren {L L' ρε} (wρε : well_Fweakening ρε L L')
  (i : list_index L') : index_to_nat (ren_index wρε i) = wk_to_ren ρε (index_to_nat i).
Proof.
  induction wρε.
  + inversion i.
  + cbn. eapply (f_equal S), IHwρε.
  + revert wρε f IHwρε.
    pattern L', F', i.
    induction i using index_case.
    - intros. cbn. reflexivity.
    - intros. cbn. eapply (f_equal S), IHwρε.
Qed.
Lemma well_Fwk_in (L L' : list Fcontext) (ρε : Fweakening) (wρε : well_Fweakening ρε L' L) (i : list_index L)
  (n : nat) (b : bool) (hin : in_Fctx (list_at L i) n b) :
  in_Fctx (list_at L' (ren_index wρε i)) n b.
Proof.
  induction wρε.
  + inversion i.
  + cbn. auto.
  + revert wρε f hin IHwρε. induction i using index_caseS; intros.
    - cbn in *. eapply f, hin.
    - cbn in *. eapply IHwρε, hin.
Qed.

(** ** Well-formed weakenings between two contexts *)

(** To avoid dependency issues, we define well-formed weakenings as
a predicate on raw weakenings defined above, rather than directly
using indexed weakenings. *)

Inductive well_weakening (ρε : Fweakening) :
    weakening -> Tcontext -> Tcontext -> Type :=
  | well_empty : well_weakening ρε _wk_empty nil nil
  | well_step {Γ Δ : Tcontext} (A : term) (ρ : weakening) :
    well_weakening ρε ρ Γ Δ -> well_weakening ρε (_wk_step ρ) (cons A Γ) Δ
  | well_up {Γ Δ : Tcontext} (A : term) (ρ : weakening) :
    well_weakening ρε ρ Γ Δ -> well_weakening ρε (_wk_up ρ) (cons A⟨ρ;wk_to_ren ρε⟩ Γ) (cons A Δ).

Derive Signature for well_weakening.

Lemma well_wk_irr {ρε} : forall ρ Γ Δ (w1 w2 : well_weakening ρε ρ Γ Δ), w1 = w2.
Proof.
induction w1.
+ now depelim w2.
+ depelim w2; now f_equal.
+ depelim w2.
  replace e' with (@eq_refl _ (A⟨ρ; wk_to_ren ρε⟩)) in H by apply eqdec_uip, term_EqDec.
  cbn in H; rewrite H; now f_equal.
Qed.
Definition Fwk_id {F} : F ≤ε F := fun n b hin => hin.
Definition well_Fwk_id {L} : well_Fweakening (_wk_id L) L L.
Proof.
  induction L; cbn; constructor; tea.
  eapply Fwk_id.
Qed.

Lemma well_wk_id {L : list Fcontext} (Γ : Tcontext) : well_weakening (_wk_id L) (_wk_id Γ) Γ Γ.
Proof.
  induction Γ as [|d].
  1: econstructor.
  replace d with (d⟨wk_to_ren (_wk_id Γ); wk_to_ren (_wk_id L)⟩) at 2.
  1: now econstructor.
  rewrite (@wk_to_ren_id' Fcontext).
  rewrite wk_to_ren_id.
  asimpl.
  eapply idRen_alpha.
Qed.


Definition Fwk_compose {Γ Γ' Γ''} : Γ ≤ε Γ' -> Γ' ≤ε Γ'' -> Γ ≤ε Γ'' := fun ρ ρ' n b hin => ρ n b (ρ' n b hin).
Definition well_Fwk_compose {ρ ρ' : Fweakening} {L L' L'' : list Fcontext}:
  well_Fweakening ρ L L' -> well_Fweakening ρ' L' L'' -> well_Fweakening (wk_compose ρ ρ') L L''.
Proof.
  intros hρ hρ'.
  induction hρ as [| | ? ? ? ν] in ρ', L'', hρ' |- *.
  1,2: cbn.
  - tea.
  - econstructor. auto.
  - inversion hρ' as [| | ? ? A' ν']; subst ; clear hρ'.
    1: now econstructor ; auto.
    constructor; auto.
    now eapply Fwk_compose.
Defined.


Lemma well_wk_compose {ρε ρε'} {ρ ρ' : weakening} {Δ Δ' Δ'' : Tcontext} :
  well_weakening ρε ρ Δ Δ' -> well_weakening ρε' ρ' Δ' Δ'' -> well_weakening (wk_compose ρε ρε') (wk_compose ρ ρ') Δ Δ''.
Proof.
  intros H H'.
  induction H as [| | ? ? ? ν] in ρ', Δ'', H' |- *.
  all: cbn.
  - inversion H'; subst; constructor.
  - econstructor. auto.
  - inversion H' as [| | ? ? A' ν']; subst ; clear H'.
    1: now econstructor ; auto.
    unfold ren1, Ren1_wk. rewrite commRen_alpha_term. unfold funcomp.
    rewrite compRen_alpha, renRen_term.
    erewrite extRen_term, extRen_alpha ; refold.
    2,3: symmetry ; now apply wk_compose_compose.
    econstructor; auto.
Qed.


#[projections(primitive)]Record wk_well_wk {Γ Δ : context} := {
  Fwk :> Fweakening;
  well_Fwk :> well_Fweakening Fwk (Fctx Γ) (Fctx Δ);
  wk :> weakening ;
  well_wk :> well_weakening Fwk wk (Tctx Γ) (Tctx Δ)
}.
Arguments wk_well_wk : clear implicits.
Arguments Build_wk_well_wk : clear implicits.
Notation "Γ ≤ Δ" := (wk_well_wk Γ Δ).


Lemma wk_well_wk_wk_eq : forall Γ Δ (ρ1 ρ2 : Γ ≤ Δ),
  ρ1.(wk) = ρ2.(wk) -> ρ1.(Fwk) = ρ2.(Fwk) -> ρ1 = ρ2.
Proof.
intros Γ Δ [ρε1 wε1 ρ1 w1] [ρε2 wε2 ρ2 w2]; cbn; intros <- <-.
assert (eε : wε1 = wε2) by apply well_Fwk_irr; destruct eε;
assert (e : w1 = w2) by apply well_wk_irr; now destruct e.
Qed.

#[global] Hint Resolve well_wk : core.

(** ** Instance: how to rename by a well-formed weakening. *)


#[global] Instance Ren1_well_wk {Z : Type} `{Ren1 (nat -> nat) term Z} {Γ Δ : context} :
  (Ren1 (Γ ≤ Δ) term Z) :=
  fun ρ t => t ⟨(wk_to_ren ρ) ; (wk_to_ren ρ.(Fwk))⟩.

Arguments Ren1_well_wk {_ _ _ _} _ _/.

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
(* Definition Fwk_empty : ε ≤ε ε := fun n b hin => hin. *)
Definition wk_empty : (ε ≤ ε) :=
  Build_wk_well_wk ε ε _wk_empty well_emptyF _wk_empty (well_empty _).


(* Definition _Fwk_step {Γ Δ : context} {A}: Γ ≤ε Δ -> (Γ,,A) ≤ε Δ := fun ρ n b hin => (ρ n b hin). (* For symmetry. Fwk_id should always work *) *)
Definition wk_step {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,A) ≤ Δ :=
  Build_wk_well_wk (Γ,,A) Δ ρ ρ (_wk_step ρ) (well_step ρ A ρ ρ).

(* Definition Fwk_up {Γ Δ A} (ρ : Γ ≤ Δ): (Γ,, A⟨ρ⟩) ≤ε Δ -> (Γ,,A) ≤ε Δ := fun ρ n b hin => (ρ n b hin). *)
Definition wk_up {Γ Δ} A (ρ : Γ ≤ Δ) : (Γ,,  A⟨ρ⟩) ≤ (Δ ,, A) :=
  Build_wk_well_wk (Γ,,  A⟨ρ⟩) (Δ ,, A) ρ ρ (_wk_up ρ) (well_up ρ A ρ ρ).


Definition wk_id {Γ} : Γ ≤ Γ :=
  Build_wk_well_wk Γ Γ (_wk_id (Fctx Γ)) well_Fwk_id  (_wk_id (Tctx Γ)) (well_wk_id (Tctx Γ)).

(* Definition wk_Fwk {Γ: context} {L} (ρF : L ≤ε Γ) : (Build_context Γ L) ≤ Γ :=
  Build_wk_well_wk (Build_context Γ L) _ (_wk_id Γ) (well_wk_id Γ) ρF. *)

Definition wk_well_wk_compose {Γ Γ' Γ'' : context} (ρ : Γ ≤ Γ') (ρ' : Γ' ≤ Γ'') : Γ ≤ Γ'' := {|
  Fwk := wk_compose ρ.(Fwk) ρ'.(Fwk);
  well_Fwk := well_Fwk_compose ρ ρ';
  wk := wk_compose ρ.(wk) ρ'.(wk);
  well_wk := well_wk_compose ρ.(well_wk) ρ'.(well_wk)
  |}.
Notation "ρ ∘w ρ'" := (wk_well_wk_compose ρ ρ').

(** ** The ubiquitous operation of adding one variable at the end of a context *)

Definition wk1 {Γ} A : Γ,, A ≤ Γ := wk_step A (wk_id (Γ := Γ)).

Lemma well_length {Γ Δ : context} (ρ : Γ ≤ Δ) : #|Tctx Δ| <= #|Tctx Γ|.
Proof.
  destruct ρ as [?? ρ wellρ].
  induction wellρ.
  all: cbn ; lia.
Qed.


Lemma id_ren (Γ : context) (ρ : Γ ≤ Γ) : ρ.(wk) = (_wk_id (Tctx Γ)).
Proof.
  destruct ρ as [ρε wρε ρ wρ] ; cbn.
  destruct Γ as [Γ L]; cbn in *.
(*   pose proof (@eq_refl _ #|Fctx Γ|) as eFΓ. *)
  pose proof (@eq_refl _ #|Γ|) as eΓ.
  revert (* eFΓ *) eΓ wρε wρ.
  generalize Γ at 2 4.
  intros Δ eΔ ??.
  induction wρ in eΔ |- *.
  all: cbn.
  - reflexivity.
  - set (Γ' := (Build_context Γ L)).
    set (Δ' := (Build_context Δ L)).
    pose proof (well_length (Build_wk_well_wk Γ' Δ' ρε wρε ρ wρ )).
    now cbn in * ; lia.
  - rewrite IHwρ.
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

(** Substitutions **)

#[projections(primitive)]Record substitution := mk_subst {
  subst_subst : nat -> term;
  subst_alpha : nat -> nat
}.

Definition substitute (σ : substitution) (t : term) := (ren_alpha (subst_alpha σ) t)[subst_subst σ].

#[global] Instance Subst_alpha : (Subst1 _ _ _) := substitute.

Lemma upRen_alpha_subst_pointwise {σ ρε}: up_term_term (σ >> ren_alpha ρε) =1 up_term_term σ >> ren_alpha ρε.
Proof. unfold up_term_term. fsimpl. rewrite commRen_alpha_term_pointwise. reflexivity. Qed.

Lemma substRen_alpha_pointwise σ ρε: subst_term σ >> ren_alpha ρε =1
  ren_alpha ρε >> subst_term (σ >> ren_alpha ρε).
Proof.
  intros t; revert σ.
  induction t; intros ?; cbn; f_equal; try easy;
  [..|rewrite upRen_alpha_subst_pointwise];
  now rewrite upRen_alpha_subst_pointwise.
Qed.
Lemma substRen_alpha σ ρε t : ren_alpha ρε (subst_term σ t) =
  (ren_alpha ρε >> subst_term (σ >> ren_alpha ρε)) t.
Proof. exact (substRen_alpha_pointwise _ _ _). Qed.
(* Lemma sconsRen_alpha_pointwise σ t ρε : (t .: σ) >> ren_alpha ρε =1 (ren_alpha ρε t) .: (σ >> ren_alpha ρε).
Proof. intros []; reflexivity. Qed.
Lemma sconsRen_alpha σ t ρε x: ren_alpha ρε ((t .: σ) x) = ((ren_alpha ρε t) .: (σ >> ren_alpha ρε)) x.
Proof. exact (sconsRen_alpha_pointwise _ _ _ _). Qed. *)

Definition ren_alpha_substitution ρ σ : substitution :=
  mk_subst (fun x => ren_alpha ρ (σ.(subst_subst) x)) (σ.(subst_alpha) >> ρ).

Instance ren_substitution {X : Type} `{Ren1 X (nat -> term) (nat -> term)} : Ren1 X substitution substitution :=
  fun ρ σ => mk_subst σ.(subst_subst)⟨ρ⟩ σ.(subst_alpha).

Instance wk_substitution {Γ Δ} : Ren1 (Δ ≤ Γ) substitution substitution :=
  fun ρ σ => (ren_alpha_substitution ρ.(Fwk) σ)⟨ρ.(wk)⟩.
Definition up_subst σ : substitution := mk_subst (up_term_term σ.(subst_subst)) σ.(subst_alpha).
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
    | progress setoid_rewrite idRen_alpha_pointwise
    | progress setoid_rewrite idRen_alpha
    | progress setoid_rewrite commRen_alpha_term_pointwise
    | progress setoid_rewrite commRen_alpha_term
    | progress setoid_rewrite compRen_alpha_pointwise
    | progress setoid_rewrite compRen_alpha
    | progress setoid_rewrite upRen_alpha_subst_pointwise
    | progress setoid_rewrite substRen_alpha_pointwise
    | progress setoid_rewrite substRen_alpha
    | progress setoid_rewrite varLRen'_term_pointwise
    | progress setoid_rewrite varLRen'_term
    | progress setoid_rewrite varL'_term_pointwise
    | progress setoid_rewrite varL'_term
    | progress setoid_rewrite rinstId'_term_pointwise
    | progress setoid_rewrite rinstId'_term
    | progress setoid_rewrite instId'_term_pointwise
    | progress setoid_rewrite instId'_term
    | progress setoid_rewrite wk_to_ren_id'
    | progress setoid_rewrite wk_compose_compose
    | progress setoid_rewrite id_ren
    | progress setoid_rewrite wk1_ren
    | progress setoid_rewrite scons_eta' (** missing from AutoSubst's database? *)
    | progress unfold
        up_term_term, upRen_term_term, up_ren, wk_well_wk_compose,
        wk_id, wk_step, wk_up, wk_empty (**, _wk_up, _wk_step *)
    | progress cbn[subst_term subst_subst up_subst subst_alpha ren_term ren_alpha wk Fwk wk_to_ren]
    | progress fsimpl ]).

Ltac bsimpl := check_no_evars;
                repeat
                 unfold VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_term, Subst1, subst1,
                  Ren1_subst, Ren1_wk, Ren1_well_wk,
                  Subst_alpha, substitute, wk_substitution, ren_alpha_substitution, ren_substitution
                  in *; bsimpl'; minimize.

(** ** Weakenings play well with context access *)

Lemma ren2_alpha_shift t ρ ρε : t⟨ρ >> S; ρε⟩ = t⟨ρ; ρε⟩⟨↑⟩.
Proof. now asimpl. Qed.

Lemma shift_upRen_eq : forall {t : term} {ρ : nat -> nat}, t⟨↑⟩⟨upRen_term_term ρ⟩ = t⟨ρ⟩⟨↑⟩.
Proof.
  intros t ρ.
  now bsimpl.
Qed.

Lemma shift_upRen2_eq : forall {t : term} {ρ : nat -> nat} ρε, t⟨↑⟩⟨upRen_term_term ρ; ρε⟩ = t⟨ρ; ρε⟩⟨↑⟩.
Proof.
  intros. now bsimpl.
Qed.

Lemma in_ctx_wk (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Γ n decl ->
in_ctx Δ (ρ n) (decl⟨ρ⟩).
Proof.
  intros Hdecl.
  destruct ρ as [ρε wfρε ρ wfρ]; cbn in *.
  change Γ with (Build_context Γ Γ) in Hdecl; change Δ with (Build_context Δ Δ). unfold in_ctx, ren1 in *; cbn in *.
  induction wfρ in n, decl, Hdecl |- *.
  - inversion Hdecl.
  - cbn.
    rewrite ren2_alpha_shift.
    now econstructor.
  - destruct n ; cbn.
    + inversion Hdecl ; subst ; clear Hdecl.
      rewrite shift_upRen2_eq.
      now constructor.
    + inversion Hdecl ; subst ; cbn in * ; refold.
      rewrite shift_upRen2_eq.
      now econstructor.
Qed.

Lemma in_ctx_str (Γ Δ : context) n decl (ρ : Δ ≤ Γ) :
in_ctx Δ (ρ n) decl ->
∑ decl', decl = decl'⟨ρ⟩ × in_ctx Γ n decl'.
Proof.
intros Hdecl.
destruct ρ as [ρε wfρε ρ wfρ] ; destruct Γ, Δ; unfold in_ctx; cbn in *.
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
  unfold ren1 at 3, Ren1_well_wk; cbn.
  now rewrite shift_upRen2_eq.
+ inversion Hdecl ; subst ; clear Hdecl ; cbn in *.
  edestruct IHwfρ as [? []]; tea ; subst.
  eexists ; split.
  2: now econstructor.
  symmetry; eapply shift_upRen2_eq.
Qed.

(** Lemmas for easier rewriting *)

(** Note: should be unnecessary since scons_eta' is in bsimpl now… *)
Lemma upren_subst_rel0 t : t[(tRel 0)]⇑ = t.
Proof. now bsimpl. Qed.




Lemma ren_alpha_subst t (σ : nat -> term) ρε : (ren_alpha ρε t)[fun x => ren_alpha ρε (σ x)] = ren_alpha ρε t[σ].
Proof. now bsimpl. Qed.

Lemma subst_ren (ρ: weakening) (σ : nat -> term) t : t[σ]⟨ρ⟩ = t[σ⟨ρ⟩].
Proof.
  now bsimpl.
Qed.

Lemma subst_ren_wk {Γ Δ A} {σ : substitution} (ρ : Δ ≤ Γ) : A[σ]⟨ρ⟩ = A[σ⟨ρ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_upren t σ ρ : t[up_term_term σ]⟨upRen_term_term ρ⟩ = t[up_term_term σ⟨ρ⟩].
Proof. asimpl; unfold Ren1_subst; asimpl; substify; now asimpl. Qed.

Lemma eq_upwk {Γ Δ} A t σ (ρ : Δ ≤ Γ) : t[(up_subst σ)⟨wk_up A ρ⟩] = t[up_subst σ⟨ρ⟩].
Proof.
  bsimpl.
  apply ext_term.
  intros [].
  + reflexivity.
  + cbn. now bsimpl.
Qed.

Lemma eq_upren' σ ρ : (up_term_term σ)⟨upRen_term_term ρ⟩ =1 up_term_term σ⟨ρ⟩.
Proof.
  intros [].
  - reflexivity.
  - asimpl; unfold Ren1_subst; asimpl; substify; now asimpl.
Qed.

Lemma ren_subst (σ : nat -> term) X (ρ : X) `{Ren1 X term term} (x : nat) : σ⟨ρ⟩ x = (σ x)⟨ρ⟩ :> term.
Proof.
  asimpl; unfold Ren1_subst; now asimpl.
Qed.

Definition ext_alpha t σ τ : σ.(subst_subst) =1 τ.(subst_subst) -> σ.(subst_alpha) =1 τ.(subst_alpha) -> t[σ] = t[τ].
Proof.
  intros esubst ealpha.
  unfold subst1, Subst_alpha, substitute.
  rewrite (extRen_alpha _ _ ealpha).
  now eapply ext_term.
Qed.

Lemma ext_term_inv σ τ : (forall t, t[σ] = t[τ]) -> subst_subst σ =1 subst_subst τ.
Proof. intros Hστ n. apply (Hστ (tRel n)). Qed.

Lemma eq_upwk' {Γ Δ} A σ (ρ : Δ ≤ Γ) : subst_subst (up_subst σ)⟨wk_up A ρ⟩ =1 subst_subst (up_subst σ⟨ρ⟩).
Proof.
  apply ext_term_inv. intros t.
  eapply eq_upwk.
Qed.

Lemma eq_upupren t σ ρ : t[up_term_term (up_term_term σ)]⟨upRen_term_term (upRen_term_term ρ)⟩ =
 t[up_term_term (up_term_term σ⟨ρ⟩)].
Proof. asimpl; unfold Ren1_subst; asimpl; substify; now asimpl. Qed.


Lemma up_subst_ext σ τ : subst_subst σ =1 subst_subst τ ->
  subst_subst (up_subst σ) =1 subst_subst (up_subst τ).
Proof.
  intros hστ x.
  induction x.
  + cbn. reflexivity.
  + cbn. now rewrite hστ.
Qed.

Lemma eq_upupren' {Γ Δ} A B t σ (ρ : Δ ≤ Γ) :
  t[up_subst (up_subst σ)]⟨wk_up A (wk_up B ρ)⟩ = t[up_subst (up_subst σ⟨ρ⟩)].
Proof.
  rewrite subst_ren_wk, eq_upwk.
  eapply ext_term; intros x.
  eapply up_subst_ext, eq_upwk'.
Qed.

Lemma subst_ren_up {P n} (ρ : nat -> nat ): P[n..]⟨ρ⟩ = P⟨upRen_term_term ρ⟩[n⟨ρ⟩..].
Proof.
  now bsimpl.
Qed.

Lemma subst_ren_alpha {P n} ρε : ren_alpha ρε P[n..] = (ren_alpha ρε P)[(ren_alpha ρε n)..].
Proof.
  now bsimpl.
Qed.

Lemma subst_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P⟨wk_up A ρ⟩[n⟨ρ⟩..].
Proof.
  now bsimpl.
Qed.

(* Lemma subst1_ren_wk_up {Γ Δ P A n} (ρ : Γ ≤ Δ) : P[n .: ρ >> tRel] = P⟨wk_up A ρ⟩[n..].
Proof. bsimpl. Qed. *)

Lemma subst_ren_wk_up2 {Γ Δ P A B a b} (ρ : Γ ≤ Δ):
  P[a .: b..]⟨ρ⟩ = P⟨wk_up A (wk_up B ρ)⟩[a⟨ρ⟩ .: b⟨ρ⟩..].
Proof. now bsimpl. Qed.

(* Lemma subst_ren_subst_mixed {Γ Δ P n} (ρ : Γ ≤ Δ): P[n..]⟨ρ⟩ = P[n⟨ρ⟩ .: ρ >> tRel].
Proof. now bsimpl. Qed. *)

(* Lemma subst_ren_subst_mixed2 {Γ Δ P a b} (ρ : Γ ≤ Δ): P[a .: b..]⟨ρ⟩ = P[a⟨ρ⟩ .: (b⟨ρ⟩ .: ρ >> tRel)].
Proof. now bsimpl. Qed. *)

(* Lemma subst_ren_subst_mixed3 {Γ Δ Ξ P n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) :
  P[n⟨ρ⟩ .: ρ ∘w ρ' >> tRel] = P[n .: ρ' >> tRel]⟨ρ⟩.
Proof. now bsimpl. Qed. *)


(* Lemma wk_up_ren_subst {Γ Δ Ξ P A n}  (ρ : Γ ≤ Δ) (ρ' : Δ ≤ Ξ) :
  P[n .: ρ ∘w ρ' >> tRel] = P⟨wk_up A ρ'⟩[n .: ρ >> tRel].
Proof. now bsimpl. Qed. *)

(* Lemma shift_subst_scons {B a Γ Δ} (ρ : Δ ≤ Γ) : B⟨↑⟩[a .: ρ >> tRel] = B⟨ρ⟩.
Proof. bsimpl; now rewrite rinstInst'_term. Qed. *)

Lemma shift_subst1' {B a} : B⟨↑⟩[a..] = B.
Proof. now bsimpl. Qed.

Lemma shift_upRen ρ t : t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨upRen_term_term ρ⟩.
Proof. now asimpl. Qed.

Lemma wk_comp_ren_on {Γ Δ Ξ} (H : term) (ρ1 : Γ ≤ Δ) (ρ2 : Δ ≤ Ξ) :
  H⟨ρ2⟩⟨ρ1⟩ = H⟨ρ1 ∘w ρ2⟩.
Proof. now bsimpl. Qed.

Lemma wk_id_ren_on Γ (H : term) : H⟨@wk_id Γ⟩ = H.
Proof. bsimpl. unfold _wk_id. now bsimpl. Qed.

Lemma wk1_ren_on Γ F (H : term) : H⟨@wk1 Γ F⟩ = H⟨↑⟩.
Proof. now bsimpl. Qed.

Lemma shift_subst1 {Γ A B a} : B⟨@wk1 Γ A⟩[a..] = B.
Proof. now rewrite wk1_ren_on, shift_subst1'. Qed.

Lemma wk_up_ren_on Γ Δ (ρ : Γ ≤ Δ) F (H : term) : H⟨wk_up F ρ⟩ = H⟨upRen_term_term ρ; Fwk ρ⟩.
Proof. reflexivity. Qed.

(* Lemma wk_up_wk1_ren_on Γ F G (H : term) : H⟨wk_up F (@wk1 Γ G)⟩ = H⟨upRen_term_term ↑⟩.
Proof. now bsimpl. Qed.
 *)


Lemma wk_step_wk1 {A Γ Δ} {t : term} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟩ = t⟨wk_step A ρ⟩.
Proof.  now bsimpl. Qed.

Lemma wk_up_wk1 {A Γ Δ} {t : term} (ρ : Δ ≤ Γ) :  t⟨ρ⟩⟨@wk1 Δ A⟨ρ⟩⟩ = t⟨@wk1 Γ A⟩⟨wk_up A ρ⟩.
Proof. now bsimpl. Qed.

Lemma wk1_eta {Γ A t} : t⟨wk_up A (@wk1 Γ A)⟩[(tRel 0)..] = t.
Proof. now bsimpl. Qed.


Notation eta_expand' Γ A f := (tApp f⟨@wk1 Γ A⟩ (tRel 0)) (only parsing).

Lemma wk_prod {A B Γ Δ} (ρ : Δ ≤ Γ) : tProd A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tProd A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now bsimpl. Qed.
Notation arr' Γ A B := (tProd A B⟨@wk1 Γ A⟩).
Lemma wk_arr' {A B Γ Δ} (ρ : Δ ≤ Γ) : arr' Δ A⟨ρ⟩ B⟨ρ⟩ = (arr' Γ A B)⟨ρ⟩.
Proof. now rewrite wk_up_wk1. Qed.

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
Notation comp' Γ A f g := (tLambda A (tApp f⟨@wk1 Γ A⟩ (tApp g⟨@wk1 Γ A⟩ (tRel 0)))).
Lemma wk_comp' {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp' Γ A f g)⟨ρ⟩ = comp' Δ A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now rewrite 2wk_up_wk1. Qed.

Lemma wk_emptyElim {Γ Δ P n} (ρ : Δ ≤ Γ) :
  tEmptyElim P⟨wk_up tEmpty ρ⟩ n⟨ρ⟩ = (tEmptyElim P n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_nSucc {n t Γ Δ} (ρ : Δ ≤ Γ) : (nSucc n t)⟨ρ⟩ = nSucc n t⟨ρ⟩.
Proof. unfold ren1, Ren1_well_wk. now rewrite nSucc_ren_alpha, nSucc_ren. Qed.
Lemma wk_nat_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (nat_to_term n)⟨ρ⟩ = nat_to_term n.
Proof. eapply (wk_nSucc (t:= tZero)). Qed.
Lemma wk_succ {n Γ Δ} (ρ : Δ ≤ Γ) : (tSucc n)⟨ρ⟩ = tSucc n⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; f_equal. now bsimpl.
Qed.
Lemma wk_natElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tNatElim P⟨wk_up tNat ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tNatElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_elimLeafHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimLeafHypTy P⟨wk_up A ρ⟩ = (elimLeafHypTy P)⟨ρ⟩.
Proof. unfold elimLeafHypTy; cbn. f_equal ; now bsimpl. Qed.
Lemma wk_elimNodeHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimNodeHypTy P⟨wk_up A ρ⟩ = (elimNodeHypTy P)⟨ρ⟩.
Proof. unfold elimNodeHypTy; cbn; f_equal; f_equal; f_equal; f_equal; [ | f_equal]; now bsimpl. Qed.
Lemma wk_treeElim {Γ Δ P hl hn t} (ρ : Δ ≤ Γ) :
  tTreeElim P⟨wk_up tTree ρ⟩ hl⟨ρ⟩ hn⟨ρ⟩ t⟨ρ⟩ = (tTreeElim P hl hn t)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_bool_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (bool_to_term n)⟨ρ⟩ = bool_to_term n.
Proof. unfold ren1, Ren1_well_wk. now rewrite bool_to_term_ren_alpha, bool_to_term_ren. Qed.
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

Record wk_eq {Γ Δ} (ρ ρ' : Δ ≤ Γ) := {
  wk_eq1 : ρ =1 ρ';
  Fwk_eq1 : ρ.(Fwk) =1 ρ'.(Fwk);
  }.

Notation "ρ =₁ ρ'" := (wk_eq ρ ρ') (at level 60).

Goal forall {Γ Δ} (ρ ρ' : Δ ≤ Γ) (t : term), ρ =₁ ρ' -> t⟨ρ⟩ = t⟨ρ'⟩.
Proof.
  intros * [e eε].
  bsimpl. unfold funcomp. now rewrite e, eε.
Qed.

Lemma wk_to_ren_inj : forall Γ Δ (ρ1 ρ2 : Γ ≤ Δ),
  ρ1 =₁ ρ2 ->
  ρ1 = ρ2.
Proof.
  intros * [Heq HFeq]; apply wk_well_wk_wk_eq.
  1:{
  destruct ρ1 as [Fρ1 wFρ1 ρ1 wρ1], ρ2 as [Fρ2 wFρ2 ρ2 wρ2]; cbn in *.
(*   revert Γ Δ wρ1 Fρ1 wFρ1 Fρ2 wFρ2 ρ2 wρ2 Heq. *)
  induction ρ1 in Γ, Δ, wρ1, Fρ1, wFρ1, Fρ2, wFρ2, ρ2, wρ2, Heq, HFeq |-*; cbn in *.
  + destruct ρ2; cbn in *; first [reflexivity|exfalso].
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ,Δ; cbn in *.
      depelim wρ1; depelim wρ2.
  + destruct ρ2; cbn in *; first [apply f_equal|exfalso].
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wρ1; depelim wρ2.
      refine (IHρ1 (Build_context Γ0 L) (Build_context Γ' L') _ _ wρ1 _ _ _ wρ2 _ HFeq); tea.
      intros n; specialize (Heq n).
      now injection Heq.
    - specialize (Heq 0); discriminate Heq.
  + destruct ρ2; cbn in *; first [apply f_equal|exfalso].
    - destruct Γ,Δ; cbn in *.
      depelim wρ1; depelim wρ2.
    - specialize (Heq 0); discriminate Heq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wρ1; depelim wρ2.
      refine (IHρ1 (Build_context Γ0 L) (Build_context Δ L') _ _ wρ1 _ _ _ wρ2 _ HFeq); tea.
      intros n; specialize (Heq (S n)); cbn in Heq.
      now injection Heq. }
  1:{
  destruct ρ1 as [Fρ1 wFρ1 ρ1 wρ1], ρ2 as [Fρ2 wFρ2 ρ2 wρ2]; cbn in *; clear ρ1 wρ1 ρ2 wρ2 Heq.
  induction Fρ1 in Γ, Δ, wFρ1, Fρ2, wFρ2, HFeq |-*.
  + destruct Fρ2; cbn in *; first [reflexivity|exfalso].
    - specialize (HFeq 0); discriminate.
    - destruct Γ,Δ; cbn in *.
      depelim wFρ1; depelim wFρ2.
  + destruct Fρ2; cbn in *; first [apply f_equal|exfalso].
    - specialize (HFeq 0); discriminate HFeq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wFρ1; depelim wFρ2.
      refine (IHFρ1 (Build_context Γ L0) (Build_context Γ' L') wFρ1 _ wFρ2 _).
      intros n; specialize (HFeq n).
      now injection HFeq.
    - specialize (HFeq 0); discriminate HFeq.
  + destruct Fρ2; cbn in *; first [apply f_equal|exfalso].
    - destruct Γ,Δ; cbn in *.
      depelim wFρ1; depelim wFρ2.
    - specialize (HFeq 0); discriminate HFeq.
    - destruct Γ as [Γ L], Δ as [Γ' L']; cbn in *.
      depelim wFρ1; depelim wFρ2.
      refine (IHFρ1 (Build_context Γ L0) (Build_context Γ' L'0) wFρ1 _ wFρ2 _); tea.
      intros n; specialize (HFeq (S n)); cbn in HFeq.
      now injection HFeq. }
Qed.

Lemma _wk_comp_lunit {A} {Γ :list A} ρ : wk_compose (_wk_id Γ) ρ =1 ρ.
Proof. now bsimpl. Qed.

Lemma wk_comp_lunit_pointwise {Γ Δ} (ρ : Δ ≤ Γ) : wk_id ∘w ρ =₁ ρ.
Proof. constructor; eapply _wk_comp_lunit. Qed.
Lemma wk_comp_lunit {Γ Δ} (ρ : Δ ≤ Γ) : wk_id ∘w ρ = ρ.
Proof.
  apply wk_to_ren_inj; eapply wk_comp_lunit_pointwise.
Qed.

Lemma _wk_comp_runit {A} {Γ :list A} ρ : wk_compose ρ (_wk_id Γ) =1 ρ.
Proof. now bsimpl. Qed.
Lemma wk_comp_runit_pointwise {Γ Δ} (ρ : Δ ≤ Γ) : ρ ∘w wk_id =₁ ρ.
Proof. constructor; eapply _wk_comp_runit. Qed.
Lemma wk_comp_runit {Γ Δ} (ρ : Δ ≤ Γ) : ρ ∘w wk_id = ρ.
Proof.
  apply wk_to_ren_inj; eapply wk_comp_runit_pointwise.
Qed.

Lemma _wk_comp_assoc(*  {A} {Γ Δ Ξ ζ : list A} *) ρ ρ' ρ'' :
  wk_compose (wk_compose ρ'' ρ') ρ =1 wk_compose ρ'' (wk_compose ρ' ρ).
Proof. now bsimpl. Qed.

Lemma wk_comp_assoc_pointwise {Γ Δ Ξ ζ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) (ρ'' : ζ ≤ Ξ) :
  (ρ'' ∘w ρ') ∘w ρ =₁ ρ'' ∘w (ρ' ∘w ρ).
Proof. constructor; eapply _wk_comp_assoc. Qed.
Lemma wk_comp_assoc {Γ Δ Ξ ζ} (ρ : Δ ≤ Γ) (ρ' : Ξ ≤ Δ) (ρ'' : ζ ≤ Ξ) :
  (ρ'' ∘w ρ') ∘w ρ = ρ'' ∘w (ρ' ∘w ρ).
Proof.
  apply wk_to_ren_inj; eapply wk_comp_assoc_pointwise.
Qed.

Lemma wk1_irr {Γ Γ' A A'} {t : term} : t⟨@wk1 Γ A⟩ = t⟨@wk1 Γ' A'⟩.
Proof. intros; now rewrite 2!wk1_ren_on. Qed.

Lemma var0_wk1_id {Γ A t} : t[tRel 0 .: @wk1 Γ A >> tRel] = t.
Proof. now bsimpl. Qed.

(* Lemma eq_subst_scons {Γ} a B : B[a..] = B[a⟨@wk_id Γ⟩ .: @wk_id Γ >> tRel].
Proof. now bsimpl. Qed. *)
(* 
Lemma wk1_subst A Γ F σ : (A ⟨@wk1 Γ F⟩)[σ] = A[↑ >> σ].
Proof. asimpl; now rewrite wk1_ren. Qed.

Lemma ren_subst  {Γ Δ} A (ρ : Γ ≤ Δ) σ : A⟨ρ⟩[σ] = A[ ρ >> σ].
Proof. now asimpl. Qed.

Lemma liftSubstComm' G t σ : G[t]⇑[σ] = G[t[σ] .: ↑ >> σ].
Proof. now bsimpl. Qed.

Lemma liftSubstComm Γ F G t σ : G[t]⇑[σ] = G[t[σ] .: @wk1 Γ F >> σ].
Proof. rewrite wk1_ren; eapply liftSubstComm'. Qed. *)



Lemma Fwk_new {L L' : Fcontext} (new : newnat L) b :  L' ≤ε L -> in_Fctx L' new b ->  L' ≤ε (Fcons' L new b).
Proof.
  intros Fρ hin n' b' hin'.
  destruct new; cbn in *.
  inversion hin'; subst.
  - apply hin.
  - now apply Fρ.
Defined.

Lemma εwk_new {L L' : list Fcontext} i (new : newnat (list_at L i)) b {ρε} (wρε : well_Fweakening ρε L' L) :
  in_Fctx (list_at L' (ren_index wρε i)) new b -> well_Fweakening ρε L' (Fcons L i new b).
Proof.
  intros hin.
  induction wρε; cbn in *.
  + inversion i.
  + constructor. eapply IHwρε, hin.
  + revert wρε f hin IHwρε.
    induction i using index_case; cbn; intros.
    * constructor; tea.
      now eapply Fwk_new.
    * constructor; tea. eapply IHwρε, hin.
Defined.

Lemma wk_new : forall {Γ Δ: context} i (new : newnat (list_at Γ i)) b (ρ : Δ ≤ Γ),
  in_Fctx (list_at Δ (ren_index ρ i)) new b -> Δ ≤ (Γ,, i : new ↦ b).
Proof.
  intros Γ Δ i new b ρ hin.
  refine (Build_wk_well_wk _ _ (Fwk ρ) _ (wk ρ) _).
  + now eapply εwk_new.
  + apply ρ.
Defined.

Lemma Fwk_Fup : forall {L L'} b (Fρ :  L' ≤ε L) (new : newnat L) (new' : newnat L'),
   new = new' :> nat -> (Fcons' L' new' b) ≤ε (Fcons' L new b).
Proof.
  intros * ρε [n hnotin] [n' hnotin'] e n'' b'' hin'.
  cbn in *; destruct e.
  inversion hin'; subst; constructor.
  now apply ρε.
Defined.

Lemma wk_Fup : forall {Γ Δ} b (ρ : Δ ≤ Γ ) i (new : newnat (list_at Γ i))
  (new' : newnat (list_at Δ (ren_index ρ i))),
  new = new' :> nat -> (Δ,, (ren_index ρ i) : new' ↦ b) ≤ (Γ,, i : new ↦ b).
Proof.
  intros * e.
  destruct ρ as [ρε wρε ρ wρ]; cbn.
  unshelve eapply (Build_wk_well_wk _ _ ρε _ ρ), wρ.
  destruct Γ as [Γ L], Δ as [Δ L']; cbn in *.
  clear ρ wρ.
  induction wρε.
  - inversion i.
  - cbn. constructor.
    eapply IHwρε, e.
  - revert wρε f new new' e IHwρε.
    induction i using index_case; intros; cbn.
    * constructor; tea.
      now eapply Fwk_Fup.
    * constructor; tea.
      eapply IHwρε, e.
Defined.

Lemma wk_alphaup {Γ Δ} (ρ : Δ ≤ Γ) : Δ,,↦ ≤ Γ,,↦.
Proof.
  destruct ρ as [ρε wρε ρ wρ]; cbn.
  refine (Build_wk_well_wk (Δ,, ↦ ) (Γ,,↦) (_wk_up ρε) _ ρ _).
  + constructor; tea.
    eapply Fwk_id.
  + induction wρ; cbn in *.
    - constructor.
    - now constructor.
    - replace (ren_alpha S A⟨ρ;wk_to_ren ρε⟩) with (ren_alpha S A)⟨ρ; wk_to_ren (_wk_up ρε)⟩.
      2:{ bsimpl. rewrite <- compRen_alpha_pointwise. reflexivity. }
      now constructor.
Defined.


Definition Fwk_Fstep {L L':Fcontext} (new : newnat L') b :  L' ≤ε L ->  (Fcons' L' new b) ≤ε L:=
  fun Fρ n b hin => in_thereF _ _ _ _ _ (Fρ _ _ hin).

Lemma wk_Fstep {Γ Δ} i new b (ρ : Γ ≤ Δ) : (Γ,, i : new ↦ b) ≤ Δ.
Proof.
  destruct ρ as [ρε wρε ρ wρ]; cbn.
  refine (Build_wk_well_wk (Γ,, i : new ↦ b) Δ ρε _ _ wρ).
  destruct Γ as [Γ L], Δ as [Δ L']; cbn in *.
  clear ρ wρ.
  induction wρε as [|????ρε|].
  + inversion i.
  + induction i using index_case.
    - cbn; now constructor.
    - cbn; constructor. eapply IHwρε.
  + induction i using index_case.
    - cbn; constructor; tea.
      eapply Fwk_Fstep, f.
    - cbn; constructor; tea.
      eapply IHwρε.
Defined.


Lemma wk_Fstep_ren_on {Γ Δ} i new b (ρ : Γ ≤ Δ) (t : term) : t⟨wk_Fstep i new b ρ⟩ = t⟨ρ⟩.
Proof.
  reflexivity.
Qed.

Definition wk_alphastep {Γ Δ} (ρ : Γ ≤ Δ) : (Γ,, ↦ ) ≤ Δ.
Proof.
  destruct ρ as [ρε wρε ρ wρ]; cbn.
  refine (Build_wk_well_wk (Γ,, ↦ ) Δ (_wk_step ρε) _ ρ _).
  + now constructor.
  + induction wρ; cbn in *.
    - constructor.
    - now constructor.
    - replace (ren_alpha S A⟨ρ;wk_to_ren ρε⟩) with A⟨ρ; wk_to_ren (_wk_step ρε)⟩.
      2:{ bsimpl. rewrite <- compRen_alpha_pointwise. reflexivity. }
      now constructor.
Defined.

Lemma wk_alphastep_ren_on {Γ Δ} (ρ : Γ ≤ Δ) (t : term) : t⟨wk_alphastep ρ⟩ = ren_alpha S t⟨ρ⟩.
Proof.
  bsimpl. cbn. bsimpl.
  now rewrite <- compRen_alpha_pointwise.
Qed.

Lemma wk_new_notin {L L':Fcontext} (new : newnat L') : L' ≤ε L -> not_in_Fctx L new.
Proof.
  intros ρε.
  eapply not_in_is_notin.
  intros b hin.
  eapply notin_is_not_in, ρε, hin.
  eapply new.
Qed.



From LogRel Require Import Utils Syntax.All.

Inductive DTree (L : Fcontext) : Set :=
  | leaf : DTree L
  | node (new : newnat L):
    DTree (Fcons' L new true) ->
    DTree (Fcons' L new false) ->
    DTree L.


Arguments node {_ _}.

Fixpoint overtree {L} (d : DTree L) L' : SProp :=
  match d with
  | leaf _ => L' ≤ε L
  | @node _ new dt df =>
    match decide_in L' new with
    | is_in true _ => overtree dt L'
    | is_in false _ => overtree df L'
    | is_notin _ => SFalse
    end
  end.

Lemma overtree_Fwk {L L'} {d : DTree L} : overtree d L' -> L' ≤ε L.
Proof.
  induction d as [ | L new Lt iht Lf ihf] ; cbn ; intros H ; auto.
  destruct (decide_in L' new).
  - eapply Fwk_compose.
    destruct b.
    + now apply iht.
    + now apply ihf.
    + eapply Fwk_Fstep; apply Fwk_id. 
  - destruct H.
Qed.


Fixpoint DTree_PSh {L} L' {Fρ : L' ≤ε L} : DTree L -> DTree L'.
Proof.
  intros d.
  destruct d as [| new dt df].
  - apply leaf.
  - destruct (decide_in L' new) as [b hin |hnotin].
    + refine (DTree_PSh (Fcons' L new b) L' _ (match b with true=>dt|false=>df end)).
      now eapply Fwk_new.
    + refine (@node _ (Build_newnat L' new hnotin) _ _).
      * unshelve eapply (DTree_PSh _ _ _ dt).
        now eapply Fwk_Fup.
      * unshelve eapply (DTree_PSh _ _ _ df).
        now eapply Fwk_Fup.
Defined.

Lemma overtree_PSh (L L' L'' : Fcontext) (Fρ : L' ≤ε L) (d : DTree L) :
  overtree (DTree_PSh L' d) L'' -> overtree d L''.
Proof.
  intros Hover; assert (Fρ' : L'' ≤ε L') by now eapply overtree_Fwk.
  revert L' L'' Fρ Fρ' Hover;
  induction d as [ | L new dt iht df ihf];
  intros * Fρ' Hover; cbn in *.
  - now eapply Fwk_compose.
  - destruct (decide_in L' new) as [[] hin'|hnotin']; cbn in *;
    destruct (decide_in L'' new) as [[] hin''|hnotin''].
    1,5,9: easy.
    2,4: eauto using notin_is_not_in.
    + destruct (functionality_inversion _ new (Fρ' _ _ hin') hin'').
    + destruct (functionality_inversion _ new hin'' (Fρ' _ _ hin')).
    + refine (iht _ _ _ _ Hover).
      now eapply (Fwk_new (Build_newnat L' new hnotin') true Fρ').
    + refine (ihf _ _ _ _ Hover).
      now eapply (Fwk_new (Build_newnat L' new hnotin') false Fρ').
Qed.

Local Set Universe Polymorphism.


Definition PSh@{i} Γ : Type@{i+1} := forall (Δ : context), Δ ≤ Γ -> Type@{i}.

Definition PSh_PSh {Γ Δ} (ρ : Γ ≤ Δ): PSh Δ -> PSh Γ :=
  fun A Ξ σ => A Ξ (σ ∘w ρ).

Lemma PSh_rew {Γ} (A : PSh Γ) : forall Δ (ρ ρ' : Δ ≤ Γ), ρ =1 ρ' -> A Δ ρ -> A Δ ρ'.
Proof.
  intros Δ ρ ρ' heq1 hA.
  apply wk_to_ren_inj in heq1.
  now destruct heq1.
Qed.

Definition hom {Γ} (A B : PSh Γ) := forall Δ ρ, A Δ ρ -> B Δ ρ.

Lemma hom_PSh {Γ} {A B : PSh Γ} : hom A B -> forall Δ (ρ : Δ ≤ Γ), hom (PSh_PSh ρ A) (PSh_PSh ρ B).
Proof.
  intros hhom Δ ρ Ξ σ hA.
  apply hhom.
  apply hA.
Qed.

#[projections(primitive)] Record Split@{i} {Γ} (A : PSh@{i} Γ) : Type@{i} := {
  dtree : DTree Γ;
  cover : forall (Δ : context) ρ, overtree dtree Δ -> A Δ ρ
}.

Arguments dtree {_ _}.
Arguments cover {_ _}.

Definition Split_PSh {Γ} : PSh Γ -> PSh Γ:=
 fun A Δ ρ => Split (PSh_PSh ρ A).

Lemma split_hom_PSh Γ (A B : PSh Γ) : hom A B -> Split A -> Split B.
Proof.
  intros hhom hA.
  destruct hA as [dA hA].
  exists dA.
  intros Δ ρ hover.
  apply hhom.
  now apply hA.
Qed.

Lemma Split_wkn Γ (A : PSh Γ) : Split A -> forall Δ ρ, Split_PSh A Δ ρ.
Proof.
  intros [dA hA] Δ ρ.
  exists (DTree_PSh Δ dA).
  intros Ξ σ Hover.
  apply hA.
  now eapply overtree_PSh.
Qed.

Lemma Split_wkn_inv Γ A : (forall Δ (ρ : Δ ≤ Γ), Split_PSh A Δ ρ) -> Split A.
Proof.
  intros.
  eapply split_hom_PSh.
  2: apply (X Γ wk_id).
  intros Δ ρ hA.
  refine (PSh_rew A _ _ _ _ hA).
  bsimpl.
  reflexivity.
Qed.

Definition shf {Γ} (A : PSh Γ) := forall Δ (ρ : Δ ≤ Γ) new,
    A (Δ,,new↦true) (wk_Fstep _ _ ρ) ->
    A (Δ,,new↦false) (wk_Fstep _ _ ρ) ->
    A Δ ρ.

Lemma shf_PSh {Γ A} : shf A -> forall Δ (ρ : Δ ≤ Γ), shf (PSh_PSh ρ A).
Proof.
  intros hAshf Δ ρ Ξ σ new hAt hAf.
  unfold PSh_PSh, shf in *.
  now eapply hAshf.
Qed.

Lemma Split_shf {Γ} {A : PSh Γ} : shf (Split_PSh A).
Proof.
  intros Δ ρ new [dAt hAt] [dAf hAf].
  exists (node dAt dAf).
  intros Ξ σ hover.
  cbn in hover.
  destruct (decide_in Ξ new) as [[] hin|hnotin].
  - specialize (hAt Ξ (wk_new new true σ hin) hover).
    refine (PSh_rew A _ _ _ _ hAt).
    bsimpl. reflexivity.
  - specialize (hAf Ξ (wk_new new false σ hin) hover).
    refine (PSh_rew A _ _ _ _ hAf).
    bsimpl. reflexivity.
  - destruct hover.
Qed.


Lemma split_bind_alg : forall Γ (A B: PSh Γ),
  shf B ->
  hom A B ->
  Split A -> (forall Δ (ρ : Δ ≤ Γ), B Δ ρ).
Proof.
  intros [Γ L] A B hBshf hhom [dA hA]; cbn in *.
  induction dA as [L |L new dt ihAt df ihAf].
  - intros Δ ρ. cbn in *.
    apply hhom.
    apply hA.
    apply ρ.
  - change L with (Fctx (Build_context Γ L)) in new.
    specialize (ihAt (PSh_PSh (wk_Fstep new true wk_id) A)
      (PSh_PSh (wk_Fstep new true wk_id) B) (shf_PSh hBshf _ _) (hom_PSh hhom _ _)).
    specialize (ihAf (PSh_PSh (wk_Fstep new false wk_id) A)
      (PSh_PSh (wk_Fstep new false wk_id) B) (shf_PSh hBshf _ _) (hom_PSh hhom _ _)).
    assert (forall (b: bool) Δ (ρ : Δ ≤ (Build_context Γ L),,new ↦ b),
      overtree (match b with true => dt| false => df end) Δ -> PSh_PSh (wk_Fstep new b wk_id) A Δ ρ) as H.
    1:{ intros b Δ ρ hover.
        apply hA; cbn.
        rewrite (decide_in_in Δ new b (Fwk ρ new b (in_hereF L new b))).
        now destruct b. }
    specialize (ihAt (H true)).
    specialize (ihAf (H false)).
    clear H.
    intros Δ ρ.
    destruct (decide_in Δ new) as [[] hin|hnotin].
    + specialize (ihAt Δ (wk_new new true ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAt).
      bsimpl. reflexivity.
    + specialize (ihAf Δ (wk_new new false ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAf).
      bsimpl. reflexivity.
    + set (new' := Build_newnat Δ new hnotin).
      eapply hBshf.
      * specialize (ihAt (Δ,, new' ↦ true) (wk_Fup _ _ true new ρ new new')).
        refine (PSh_rew B _ _ _ _ ihAt).
        bsimpl. reflexivity.
      * specialize (ihAf (Δ,, new' ↦ false) (wk_Fup _ _ false new ρ new new')).
        refine (PSh_rew B _ _ _ _ ihAf).
        bsimpl. reflexivity.
Qed.


Lemma Split_bind : forall Γ (A B : PSh Γ),
  Split A ->
  (forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Split_PSh B Δ ρ) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  apply (split_bind_alg Γ A).
  - apply Split_shf.
  - exact f.
  - apply hA.
Qed.

(* 
Definition dover {Γ} {A : PSh Γ} (P : forall Δ ρ, A Δ ρ -> Type)
  (hA : Split A) := forall L (hover : overtree hA.(dtree) L),
  P (Build_context Γ L) (wk_Fwk (overtree_Fwk hover)) (hA.(cover) (wk_Fwk (overtree_Fwk hover)) hover).
 *)

Definition dover {Γ} {A : PSh Γ} (P : forall Δ ρ, A Δ ρ -> Type)
  (hA : Split A) := forall Δ (ρ : Δ ≤ Γ) (hover : overtree hA.(dtree) Δ),
  P Δ ρ (hA.(cover) Δ ρ hover).

Definition dover_apply {Γ} {A : PSh Γ} {P Q: forall Δ ρ, A Δ ρ -> Type} {hA : Split A} :
  (forall {Δ ρ a}, P Δ ρ a -> Q Δ ρ a) -> dover P hA -> dover Q hA :=
 (fun f hdover Δ ρ hover => f Δ ρ _ (hdover _ _ _)).

Definition ddover {Γ} {A : PSh Γ} {P: forall Δ ρ, A Δ ρ -> Type} (Q : forall Δ ρ a, P Δ ρ a -> Type) {hA : Split A} :
  dover P hA -> Type :=
 (fun hdover => forall Δ ρ hover, Q Δ ρ _ (hdover _ _ hover)).



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

Lemma over_DTree_PSh (L L' L'' : Fcontext) (Fρ : L' ≤ε L) (d : DTree L) :
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

Lemma overtree_PSh {L L' L'' : Fcontext} {Fρ : L'' ≤ε L'} (d : DTree L) :
  overtree d L' -> overtree d L''.
Proof.
  intros.
  induction d as [ | L new dt iht df ihf].
  + now eapply Fwk_compose.
  + cbn in *.
    destruct (decide_in L' new) as [[] hin'|hnotin'].
    - rewrite (decide_in_in L'' new _ (Fρ _ _ hin')).
      now apply iht.
    - rewrite (decide_in_in L'' new _ (Fρ _ _ hin')).
      now apply ihf.
    - destruct H.
Qed.

Local Set Universe Polymorphism.


Definition PSh@{i} Γ : Type@{i+1} := forall (Δ : context), Δ ≤ Γ -> Type@{i}.

Definition PSh_PSh {Γ Δ} (ρ : Γ ≤ Δ): PSh Δ -> PSh Γ :=
  fun A Ξ σ => A Ξ (σ ∘w ρ).

Lemma PSh_rew {Γ} (A : PSh Γ) : forall {Δ} (ρ ρ' : Δ ≤ Γ), ρ =1 ρ' -> A Δ ρ -> A Δ ρ'.
Proof.
  intros Δ ρ ρ' heq1 hA.
  apply wk_to_ren_inj in heq1.
  now destruct heq1.
Qed.

Definition hom {Γ} (A B : PSh Γ) := forall Δ ρ, A Δ ρ -> B Δ ρ.

Lemma hom_PSh {Γ} {A B : PSh Γ} : hom A B -> forall {Δ} {ρ : Δ ≤ Γ}, hom (PSh_PSh ρ A) (PSh_PSh ρ B).
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

Lemma split_hom_PSh {Γ} {A B : PSh Γ} : hom A B -> Split A -> Split B.
Proof.
  intros hhom hA.
  destruct hA as [dA hA].
  exists dA.
  intros Δ ρ hover.
  apply hhom.
  now apply hA.
Qed.

Lemma Split_wkn {Γ} {A : PSh Γ} : Split A -> forall {Δ} ρ, Split (fun Ξ (ρ' : Ξ ≤ Δ) => A Ξ (ρ'∘w ρ)).
Proof.
  intros hA Δ ρ.
  exists (DTree_PSh Δ hA.(dtree)).
  intros Ξ σ Hover.
  apply hA.
  now eapply over_DTree_PSh.
Defined.

Lemma Split_wkn_inv Γ A : (forall Δ (ρ : Δ ≤ Γ), Split_PSh A Δ ρ) -> Split A.
Proof.
  intros.
  eapply split_hom_PSh.
  2: apply (X Γ wk_id).
  intros Δ ρ hA.
  refine (PSh_rew A _ _ _ hA).
  bsimpl.
  reflexivity.
Qed.

Definition shf {Γ} (A : PSh Γ) := forall Δ (ρ : Δ ≤ Γ) new,
    A (Δ,,new↦true) (wk_Fstep _ _ ρ) ->
    A (Δ,,new↦false) (wk_Fstep _ _ ρ) ->
    A Δ ρ.

Lemma shf_PSh {Γ A} : shf A -> forall {Δ} {ρ : Δ ≤ Γ}, shf (PSh_PSh ρ A).
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
    refine (PSh_rew A _ _ _ hAt).
    bsimpl. reflexivity.
  - specialize (hAf Ξ (wk_new new false σ hin) hover).
    refine (PSh_rew A _ _ _ hAf).
    bsimpl. reflexivity.
  - destruct hover.
Qed.


Lemma split_bind_alg_over : forall {Γ} {A B: PSh Γ},
  shf B -> forall (hA : Split A),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> A Δ ρ -> B Δ ρ)->
  forall Δ (ρ : Δ ≤ Γ), B Δ ρ.
Proof.
  intros [Γ L] A B hBshf [dA hA] hhom; cbn in *.
  induction dA as [L |L new dt ihAt df ihAf].
  - intros Δ ρ; cbn in *.
    apply hhom.
    2: apply hA.
    all: apply ρ.
  - change L with (Fctx (Build_context Γ L)) in new.
    specialize (ihAt (PSh_PSh (wk_Fstep new true wk_id) A)
      (PSh_PSh (wk_Fstep new true wk_id) B) (shf_PSh hBshf)).
    specialize (ihAf (PSh_PSh (wk_Fstep new false wk_id) A)
      (PSh_PSh (wk_Fstep new false wk_id) B) (shf_PSh hBshf)).
    assert (forall (b: bool) Δ (ρ : Δ ≤ (Build_context Γ L),,new ↦ b),
      overtree (match b with true => dt| false => df end) Δ -> PSh_PSh (wk_Fstep new b wk_id) A Δ ρ) as H.
    1:{ intros b Δ ρ hover.
        apply hA; cbn.
        rewrite (decide_in_in Δ new b (Fwk ρ new b (in_hereF L new b))).
        now destruct b. }
    specialize (ihAt (H true)).
    specialize (ihAf (H false)).
    clear H.
    assert (forall (b: bool) Δ (ρ : Δ ≤ (Build_context Γ L),,new ↦ b),
      overtree (match b with true => dt| false => df end) Δ ->
      PSh_PSh (wk_Fstep new b wk_id) A Δ ρ -> PSh_PSh (wk_Fstep new b wk_id) B Δ ρ) as H.
    1:{ intros b Δ ρ hover.
        apply hhom; cbn.
        rewrite (decide_in_in Δ new b (Fwk ρ new b (in_hereF L new b))).
        now destruct b. }
    specialize (ihAt (H true)).
    specialize (ihAf (H false)).
    clear H.
    intros Δ ρ.
    destruct (decide_in Δ new) as [[] hin|hnotin].
    + specialize (ihAt Δ (wk_new new true ρ hin)).
      refine (PSh_rew B _ ρ _ ihAt).
      bsimpl. reflexivity.
    + specialize (ihAf Δ (wk_new new false ρ hin)).
      refine (PSh_rew B _ ρ _ ihAf).
      bsimpl. reflexivity.
    + set (new' := Build_newnat Δ new hnotin).
      eapply hBshf.
      * specialize (ihAt (Δ,, new' ↦ true) (wk_Fup true new ρ new new')).
        refine (PSh_rew B _ _ _ ihAt).
        bsimpl. reflexivity.
      * specialize (ihAf (Δ,, new' ↦ false) (wk_Fup false new ρ new new')).
        refine (PSh_rew B _ _ _ ihAf).
        bsimpl. reflexivity.
Qed.

Lemma split_bind_alg : forall {Γ} {A B: PSh Γ},
  shf B ->
  hom A B ->
  Split A -> (forall Δ (ρ : Δ ≤ Γ), B Δ ρ).
Proof.
  intros.
  eapply (split_bind_alg_over X X1).
  intros; now eapply X0.
Qed.


Lemma Split_bind : forall {Γ} {A B : PSh Γ},
  Split A ->
  (forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  eapply (split_bind_alg); tea.
  apply Split_shf.
Qed.

Lemma Split_Splitfree {Γ} {A : PSh Γ} : Split A -> Split (fun Δ ρ => forall Ξ ρ', A Ξ (ρ'∘w ρ)).
Proof.
  intros * hA.
  exists hA.(dtree).
  intros * hover *.
  apply hA.(cover).
  now apply overtree_PSh. Show Proof.
Defined.

Lemma Split_bind_over : forall {Γ} {A B : PSh Γ} (hA :Split A),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> (forall Ξ ρ', A Ξ (ρ'∘w ρ)) -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  unshelve eapply split_bind_alg_over.
  2: apply (Split_Splitfree hA).
  1: apply Split_shf.
  apply f.
Qed.


Definition dover {Γ} {A : PSh Γ} (hA : Split A) (P : forall Δ ρ, A Δ ρ -> Type)
  := forall Δ (ρ : Δ ≤ Γ) (hover : overtree hA.(dtree) Δ),
  P Δ ρ (hA.(cover) Δ ρ hover).


Definition dover_PSh {Γ} {A : PSh Γ} {P} {hA : Split A}: dover hA P -> forall {Δ} {ρ : Δ ≤ Γ},
  dover (Split_wkn hA ρ) (fun Ξ ρ' => P Ξ (ρ'∘w ρ)).
Proof.
  intros d Δ ρ Ξ ρ' hover.
  apply d.
Qed.

Definition dSplit {Γ} {A : PSh Γ} (P : forall Δ ρ, A Δ ρ -> Type) (hA : Split A) 
  := Split (fun Δ (ρ : Δ ≤ Γ) => dover (Split_wkn hA _) (fun Ξ ρ' => P Ξ (ρ'∘w ρ))).

(* Definition irr_dPSh {Γ A} (P : forall Δ ρ, A Δ ρ -> Type) := forall Δ (ρ : Δ ≤ Γ) (a a' : A Δ ρ), P Δ ρ a -> P Δ ρ a'.

Goal forall Γ A (P : forall Δ ρ, A Δ ρ -> Type) hA, irr_dPSh P -> dSplit P hA ->
  dover (fun Δ (ρ : Δ ≤ Γ) hSplit => Split (fun Ξ ρ' => P Ξ (ρ'∘w ρ) (hSplit Ξ ρ'))) (Split_Splitfree hA).
Proof.
  intros * hirr hP Δ ρ hover.
  eapply Split_bind.
  apply (Split_wkn hP ρ).
  clear hP.
  intros Ξ ρ' hP. unfold PSh_PSh in hP.
  exists (Split_wkn hA (ρ' ∘w ρ)).(dtree).
  intros Θ ρ'' hover'.
  specialize (hP Θ ρ'' hover'). cbn in hP.
  rewrite <- wk_comp_assoc in hP.
  eapply hirr.
  apply hP. *)


Definition dover_apply {Γ} {A : PSh Γ} {P Q: forall Δ ρ, A Δ ρ -> Type} {hA : Split A} :
  (forall {Δ ρ a}, P Δ ρ a -> Q Δ ρ a) -> dover hA P-> dover hA Q:=
 (fun f hdover Δ ρ hover => f Δ ρ _ (hdover _ _ _)).

Definition ddover {Γ} {A : PSh Γ} {P: forall Δ ρ, A Δ ρ -> Type} (Q : forall Δ ρ a, P Δ ρ a -> Type) {hA : Split A} :
  dover hA P-> Type :=
 (fun hdover => forall Δ ρ hover, Q Δ ρ _ (hdover _ _ hover)).

(* 
Definition dover_to_split : forall {Γ} {A B : PSh Γ} P (hA : Split A), dover (fun Δ ρ hSplit => P _ _ hSplit -> B Δ ρ) hA ->
  dover P hA -> Split B.
Proof.
  intros * d d'.
  exists hA.(dtree).
  intros * hover.
  now unshelve eapply d.
Qed. *)

Definition dover_to_split : forall {Γ} {A B : PSh Γ} (P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type) (hA : Split A),
  (forall Δ (ρ : Δ ≤ Γ) (a : forall Ξ ρ', A Ξ (ρ'∘w ρ)),
    overtree hA.(dtree) Δ -> (forall Ξ (ρ' : Ξ ≤ Δ), P _ _ (a _ ρ')) -> Split (fun Ξ ρ' => B Ξ (ρ'∘w ρ))) ->
  dover hA P-> Split B.
Proof.
  intros * d d'.
  eapply (Split_bind_over) with (hA := Split_Splitfree hA).
  intros Δ ρ hover a.
  eapply d.
  apply hover.
  intros.
  unshelve apply d'.
  now apply overtree_PSh.
Qed.

(* 
Definition dover_to_split : forall {Γ} {A B : PSh Γ} P (hA : Split A), (forall Δ ρ, dover (fun Ξ ρ' => P Ξ (ρ'∘w ρ)) (Split_wkn hA ρ) -> B Δ ρ) ->
  dover P hA -> Split B.
Proof.
  intros * d d'.
  exists hA.(dtree).
  intros * hover.
  unshelve eapply d.
  now apply dover_PSh.
Qed.
 *)
(* 
Goal forall {Γ} {A B : PSh Γ} P (Q : forall Δ ρ, B Δ ρ -> Type) (hA : Split A) (hB : Split B),
  dover P hA -> Split (fun Δ (ρ : Δ ≤ Γ) => dover (fun Ξ ρ' hSplit => Q Ξ (ρ'∘w ρ) hSplit) (Split_wkn hB)).
Proof.
  intros * d.
  exists hA.(dtree).
  intros Δ ρ hover Ξ ρ' hover'.

 *)





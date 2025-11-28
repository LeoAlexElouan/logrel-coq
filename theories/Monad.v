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

Lemma over_DTree_PSh {L L' L'' : Fcontext} {Fρ : L' ≤ε L} (d : DTree L) :
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

Lemma over_DTree_PSh_inv (L L' L'' : Fcontext) (Fρ : L' ≤ε L) (Fρ' : L'' ≤ε L') (d : DTree L) :
  overtree d L'' -> overtree (DTree_PSh L' d) L''.
Proof.
  intros Hover.
  revert L' L'' Fρ Fρ' Hover;
  induction d as [ | L new dt iht df ihf];
  intros * Fρ' Hover; cbn in *.
  - tea.
  - destruct (decide_in L' new) as [[] hin'|hnotin']; cbn in *;
    destruct (decide_in L'' new) as [[] hin''|hnotin''].
    1,5,9: easy.
    2,4: destruct (notin_is_not_in hnotin'' (Fρ' _ _ hin')).
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

Lemma PSh_root {Γ Δ ρ} {A : PSh Γ}: (forall Ξ (ρΞ : Ξ ≤ Δ), A Ξ (ρΞ∘w ρ)) -> A Δ ρ.
Proof.
  intros hA.
  rewrite <- wk_comp_lunit.
  eapply hA.
Qed.

Definition hom {Γ} (A B : PSh Γ) := forall Δ ρ, A Δ ρ -> B Δ ρ.

Lemma hom_PSh {Γ} {A B : PSh Γ} : hom A B -> forall {Δ} {ρ : Δ ≤ Γ}, hom (PSh_PSh ρ A) (PSh_PSh ρ B).
Proof.
  intros hhom Δ ρ Ξ σ hA.
  apply hhom.
  apply hA.
Qed.

#[projections(primitive)] Record Split@{i} {Γ} (A : PSh@{i} Γ) : Type@{i} := {
  dtree :> DTree Γ;
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

Lemma Split_wkn_inv Γ A : (forall Δ (ρ : Δ ≤ Γ), Split (fun Ξ ρ' => A Ξ (ρ'∘w ρ))) -> Split A.
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

Lemma Split_shf {Γ} {A : PSh Γ} : shf (fun Δ ρ => Split (fun Ξ ρ' => A Ξ (ρ'∘w ρ))).
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

Definition over {Γ : context} (d : DTree Γ) (A: PSh Γ) := forall Δ (ρ : Δ ≤ Γ), overtree d Δ -> A Δ ρ.
(* Lemma over_PSh {Γ : context} {d : DTree Γ} {A: PSh Γ} : over d A ->
  forall Δ (ρ : Δ ≤ Γ), over (DTree_PSh Δ d) (PSh_PSh ρ A).
Proof.
  intros hA Δ ρ Ξ ρ' hover.
  apply hA.
  now eapply over_DTree_PSh.
Qed. *)

Lemma over_PSh {Γ: context} {d : DTree Γ} {A: PSh Γ} : over d A ->
  forall Δ (ρ : Δ ≤ Γ) (d' : DTree Δ), (forall Ξ (ρ' : Ξ ≤ Δ), overtree d' Ξ -> overtree d Ξ) ->over d' (PSh_PSh ρ A).
Proof.
  intros hA Δ ρ d' hdd' Ξ ρ' hover.
  now apply hA.
Qed.

Lemma over_new : forall {Γ} A {new} (b:bool) {dt df}, over (node dt df) A ->
  over (Γ:=Γ,,new↦b) (if b return _ then dt else df) (PSh_PSh  (wk_Fstep new b wk_id) A).
Proof.
  intros * hA.
  eapply over_PSh; [apply hA|].
  intros Δ ρ hover.
  cbn.
  rewrite (decide_in_in _  new b (Fwk ρ new b (in_hereF _ new b))).
  now destruct b.
Qed.

Lemma Split_bind_alg_over@{i j} : forall {Γ} {A B: PSh Γ},
  shf@{j} B -> forall (hA : Split@{i} A),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> B Δ ρ)->
  forall Δ (ρ : Δ ≤ Γ), B Δ ρ.
Proof.
  intros [Γ L] A B hBshf [dA hA] hB; cbn in *.
  induction dA as [L |L new dt ihAt df ihAf].
  - intros Δ ρ; cbn in *.
    apply hB, ρ.
  - change L with (Fctx (Build_context Γ L)) in new.
    specialize (ihAt (PSh_PSh (wk_Fstep new true wk_id) A)
      (PSh_PSh (wk_Fstep new true wk_id) B) (shf_PSh hBshf)
      (over_new A true hA) (over_new B true hB)).
    specialize (ihAf (PSh_PSh (wk_Fstep new false wk_id) A)
      (PSh_PSh (wk_Fstep new false wk_id) B) (shf_PSh hBshf)
      (over_new A false hA) (over_new B false hB)).
    intros Δ ρ.
    destruct (decide_in Δ new) as [[] hin|hnotin].
    + specialize (ihAt Δ (wk_new new true ρ hin)).
      refine (PSh_rew B _ ρ _ ihAt).
      bsimpl; reflexivity.
    + specialize (ihAf Δ (wk_new new false ρ hin)).
      refine (PSh_rew B _ ρ _ ihAf).
      bsimpl; reflexivity.
    + set (new' := Build_newnat Δ new hnotin).
      eapply hBshf.
      * specialize (ihAt (Δ,, new' ↦ true) (wk_Fup true new ρ new new')).
        refine (PSh_rew B _ _ _ ihAt).
        bsimpl. reflexivity.
      * specialize (ihAf (Δ,, new' ↦ false) (wk_Fup false new ρ new new')).
        refine (PSh_rew B _ _ _ ihAf).
        bsimpl. reflexivity.
Qed.

Lemma Split_bind_alg : forall {Γ} {A B: PSh Γ},
  shf B ->
  hom A B ->
  Split A -> (forall Δ (ρ : Δ ≤ Γ), B Δ ρ).
Proof.
  intros Γ A B hB hhom hA ??.
  eapply (Split_bind_alg_over hB hA); clear Δ ρ.
  intros ?? hoverA.
  eapply hhom.
  now eapply hA.
Qed.

(* 
Lemma Split_bind : forall {Γ} {A B : PSh Γ},
  Split A ->
  (forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  eapply (split_bind_alg); tea.
  apply Split_shf.
Qed. *)

Lemma Split_return : forall {Γ} {A: PSh Γ}, (forall Δ ρ, A Δ ρ) -> Split A.
Proof.
  intros Γ A hA.
  exists (leaf Γ).
  easy.
Qed.


Lemma Split_Splitfree {Γ} {A : PSh Γ} : Split A -> Split (fun Δ ρ => forall Ξ ρ', A Ξ (ρ'∘w ρ)).
Proof.
  intros * hA.
  exists hA.(dtree).
  intros * hover *.
  apply hA.(cover).
  now apply overtree_PSh. Show Proof.
Defined.

Lemma Split_Splitfree_inv {Γ} {A : PSh Γ} : Split (fun Δ ρ => forall Ξ ρ', A Ξ (ρ'∘w ρ)) -> Split A.
Proof.
  intros hA.
  exists hA.(dtree).
  intros * hover *.
  rewrite <- wk_comp_lunit.
  now apply hA.
Defined.

Lemma Split_bind_over: forall {Γ} {A B : PSh Γ} (hA :Split A),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  unshelve eapply Split_bind_alg_over.
  2: apply (Split_Splitfree hA).
  1: apply Split_shf.
  intros ?? hover.
  now apply f.
Qed.

Lemma Split_wk_bind_over : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (ρ : Δ ≤ Γ) {B : PSh Δ}, (forall Ξ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> Split (fun Θ (ρ'' : Θ ≤ Ξ) => B Θ (ρ''∘w ρ'))) -> Split B.
Proof.
  intros Γ A hA Δ ρ B hB.
  set (hA' := Split_wkn hA ρ).
  unshelve eapply Split_bind_over.
  2: apply hA'.
  intros Ξ ρ' hover.
  apply hB.
  cbn in hover.
  now eapply over_DTree_PSh.
Qed.

Lemma Split_wk_bind_return_over : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (ρ : Δ ≤ Γ) {B : PSh Δ}, (forall Ξ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> B Ξ ρ') -> Split B.
Proof.
  intros Γ A hA Δ ρ B hB.
  set (hA' := Split_wkn hA ρ).
  unshelve eapply Split_bind_over.
  2: apply hA'.
  intros Ξ ρ' hover.
  eapply Split_return.
  intros Θ ρΘ.
  apply hB.
  cbn in hover.
  eapply over_DTree_PSh.
  now eapply overtree_PSh.
Qed.

Lemma Split_bind_return_over: forall {Γ} {A B : PSh Γ} (hA :Split A),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ ->  B Δ ρ) ->
  Split B.
Proof.
  intros Γ A B hA f.
  unshelve eapply Split_bind_over.
  2: apply hA.
  intros ?? hover.
  apply Split_return.
  intros Ξ ρΞ.
  apply f.
  now eapply overtree_PSh.
Qed.

(* Lemma Split_bind_free : forall {Γ} {A B : PSh Γ} (hA :Split A),
  (forall Δ (ρ : Δ ≤ Γ), (forall Ξ ρ', A Ξ (ρ'∘w ρ)) -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros Γ A B hA f.
  apply Split_wkn_inv.
  unshelve eapply split_bind_alg_over.
  2: apply (Split_Splitfree hA).
  1: apply Split_shf.
  intros; now eapply f.
Qed. *)


Definition dover {Γ} {A : PSh Γ} (hA : Split A) (P : forall Δ ρ, A Δ ρ -> Type)
  := forall Δ (ρ : Δ ≤ Γ) (hover : overtree hA.(dtree) Δ),
  P Δ ρ (hA.(cover) Δ ρ hover).

Definition dover_PSh {Γ} {A : PSh Γ} {P} {hA : Split A}: dover hA P -> forall {Δ} {ρ : Δ ≤ Γ},
  dover (Split_wkn hA ρ) (fun Ξ ρ' => P Ξ (ρ'∘w ρ)).
Proof.
  intros d Δ ρ Ξ ρ' hover.
  apply d.
Qed.

Definition dover_apply {Γ} {A : PSh Γ} {P Q: forall Δ ρ, A Δ ρ -> Type} {hA : Split A} :
  (forall {Δ ρ a}, P Δ ρ a -> Q Δ ρ a) -> dover hA P-> dover hA Q:=
 (fun f hdover Δ ρ hover => f Δ ρ _ (hdover _ _ _)).

Definition ddover@{i j k} {Γ} {A : PSh@{i} Γ} {P: forall Δ ρ, A Δ ρ -> Type@{j}} (Q : forall Δ ρ a, P Δ ρ a -> Type@{k}) {hA : Split A} :
  dover hA P-> Type@{k} :=
 (fun hdover => forall Δ ρ hover, Q Δ ρ _ (hdover _ _ hover)).

Definition dSplit {Γ} {A : PSh Γ} (P : forall Δ ρ, A Δ ρ -> Type) (hA : Split A) :=
  Split (fun Δ (ρ : Δ ≤ Γ) => forall (hover : overtree hA.(dtree) Δ), P Δ ρ (hA.(cover) Δ ρ hover)).


Lemma dSplit_bind_alg_over : forall {Γ} {A B: PSh Γ} {P},
  shf B -> forall {hA : Split A} (hP : dSplit P hA),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> overtree hP.(dtree) Δ -> B Δ ρ)->
  forall Δ (ρ : Δ ≤ Γ), B Δ ρ.
Proof.
  intros Γ A B P hB hA hP hBover.
  eapply (Split_bind_alg_over hB hA).
  intros Δ ρ hoverA.
  eapply PSh_root.
  eapply (Split_bind_alg_over (shf_PSh hB) (Split_wkn hP ρ)).
  intros Ξ ρΞ hoverP.
  eapply hBover.
  now eapply overtree_PSh.
  now eapply over_DTree_PSh.
Qed.

Lemma dSplit_solve : forall Γ (A B : PSh Γ)
  (P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type) (Q : forall Δ (ρ : Δ ≤ Γ), B Δ ρ -> Type) (hA : Split A) (hB : Split B),
  (forall Δ (ρ : Δ ≤ Γ) (hoverA : overtree hA.(dtree) Δ) (hoverB : overtree hB.(dtree) Δ), P Δ ρ (hA.(cover) Δ ρ hoverA) -> Q Δ ρ (hB.(cover) Δ ρ hoverB)) ->
  dSplit P hA -> dSplit Q hB.
Proof.
  intros * hPQ d.
  eapply (Split_bind_over d).
  intros Δ ρ hover.
  exists (Split_wkn hA ρ).(dtree).
  intros Ξ ρ' hover' hover''.
  unshelve eapply hPQ.
  now eapply over_DTree_PSh.
  unshelve eapply d.
  now eapply overtree_PSh.
Qed.

Lemma Split_assoc {Γ Δ Ξ} {ρ : Δ ≤ Γ} {ρ' : Ξ ≤ Δ} {A} :
  Split (fun Θ ρ'' => A Θ (ρ'' ∘w (ρ'∘w ρ))) ->
  Split (fun Θ ρ'' => A Θ ((ρ'' ∘w ρ')∘w ρ)).
Proof.
  intros hA.
  exists hA.(dtree).
  intros Ω ρ'' hover.
  rewrite wk_comp_assoc.
  now apply hA.(cover).
Qed.

Lemma dSplit_bind_over {Γ} {A B : PSh Γ} {P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> overtree hP.(dtree) Δ -> Split (fun Ξ ρ' => B Ξ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros hB.
  eapply (Split_bind_over hA).
  intros Δ ρ hoverA.
  apply (Split_wk_bind_over hP ρ).
  intros Ξ ρ' hoverP.
  eapply Split_assoc.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

Lemma dSplit_bind_return_over {Γ} {A B : PSh Γ} {P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> overtree hP.(dtree) Δ -> B Δ ρ) ->
  Split B.
Proof.
  intros hB.
  eapply (Split_bind_over hA).
  intros Δ ρ hoverA.
  apply (Split_wk_bind_return_over hP ρ).
  intros Ξ ρ' hoverP.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

Lemma dSplit_wk_bind_over {Γ} {A : PSh Γ} {P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (ρ : Δ ≤ Γ) B, (forall Ξ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> overtree hP.(dtree) Ξ -> Split (fun Θ (ρ'' : Θ ≤ Ξ) => B Θ (ρ'' ∘w ρ'))) ->
  Split B.
Proof.
  intros Δ ρ B hB.
  eapply (Split_wk_bind_over hA ρ).
  intros Ξ ρ' hoverA.
  apply (Split_wk_bind_over hP (ρ'∘w ρ)).
  intros Θ ρ'' hoverP.
  eapply Split_assoc.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

Lemma dSplit_wk_bind_return_over {Γ} {A : PSh Γ} {P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (ρ : Δ ≤ Γ) B, (forall Ξ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> overtree hP.(dtree) Ξ -> B Ξ ρ') ->
  Split B.
Proof.
  intros Δ ρ B hB.
  eapply (Split_wk_bind_over hA ρ).
  intros Ξ ρ' hoverA.
  apply (Split_wk_bind_return_over hP (ρ'∘w ρ)).
  intros Θ ρ'' hoverP.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

(* Lemma dSplit_bind_over: forall {Γ} {A B : PSh Γ} (Q : forall Δ (ρ : Δ ≤ Γ), B Δ ρ -> Type) (hA :Split A) (hB : Split B),
  (forall Δ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> dSplit (fun Ξ ρ' hSplit=> Q Ξ (ρ' ∘w ρ) hSplit ) (Split_wkn hB ρ)) ->
  dSplit Q hB.
Proof.
  intros Γ A B Q hA hB f.
  apply Split_wkn_inv.
  unshelve eapply split_bind_alg_over.
  2: apply (Split_Splitfree hA).
  1: apply (Split_shf (A:= fun Δ ρ => forall hover, Q Δ ρ (cover hB Δ ρ hover))).
  intros Δ ρ hover _.
  specialize (f Δ ρ hover); cbn in *.
  eapply Split_bind_free; [apply f| clear f].
  intros Ξ ρ' f; cbn in *.
  exists (Split_wkn hB (ρ'∘w ρ)).(dtree).
  intros Θ ρ'' hover' hover''; cbn in *.
  assert (overtree (DTree_PSh Δ (dtree hB)) Θ).
  + eapply over_DTree_PSh_inv; tea.
    eapply (Fwk_compose ρ'' ρ').
  + specialize (f Θ ρ'' H).
    eapply f.
Qed. *)

Lemma dSplit_wkn : forall {Γ} {A : PSh Γ} (P : forall Δ (ρ : Δ ≤ Γ), A Δ ρ -> Type) (hA : Split A), dSplit P hA ->
  forall Δ (ρ : Δ ≤ Γ), dSplit (fun Ξ ρ' a=> P Ξ (ρ'∘w ρ) a) (Split_wkn hA ρ).
Proof.
  intros Γ A P hA hP Δ ρ.
  exists (DTree_PSh Δ hP.(dtree)).
  intros Ξ ρ' hover hover'.
  eapply hP.(cover).
  now eapply over_DTree_PSh.
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





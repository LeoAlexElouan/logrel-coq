From LogRel Require Import Utils Syntax.All GenericTyping.

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
Section Sheaves.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!WfContextProperties}.


  Definition PSh@{i} Γ (wfΓ : [|-Γ]): Type@{i+1} := forall (Δ : context) (wfΔ : [|-Δ]), Δ ≤ Γ -> Type@{i}.

  Definition PSh_PSh {Γ Δ wfΓ} wfΔ (ρ : Δ ≤ Γ): PSh Γ wfΓ -> PSh Δ wfΔ :=
    fun A Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ ∘w ρ).

  Lemma PSh_rew {Γ wfΓ} (A : PSh Γ wfΓ) : forall {Δ wfΔ} (ρ ρ' : Δ ≤ Γ), ρ =1 ρ' -> A Δ wfΔ ρ -> A Δ wfΔ ρ'.
  Proof.
    intros ???? heq1 hA.
    apply wk_to_ren_inj in heq1.
    now destruct heq1.
  Qed.

  Lemma PSh_root {Γ Δ wfΓ wfΔ ρ} {A : PSh Γ wfΓ}: (forall Ξ wfΞ (ρΞ : Ξ ≤ Δ), A Ξ wfΞ (ρΞ∘w ρ))
    -> A Δ wfΔ ρ.
  Proof.
    intros hA.
    rewrite <- wk_comp_lunit.
    eapply hA.
  Qed.

  Definition hom {Γ wfΓ} (A B : PSh Γ wfΓ) := forall Δ wfΔ ρ, A Δ wfΔ ρ -> B Δ wfΔ ρ.

  Lemma hom_PSh {Γ wfΓ} {A B : PSh Γ wfΓ} : hom A B -> forall {Δ wfΔ} {ρ : Δ ≤ Γ}, hom (PSh_PSh wfΔ ρ A) (PSh_PSh wfΔ ρ B).
  Proof.
    intros hhom ??? Ξ wfΞ ρΞ hA.
    apply hhom.
    apply hA.
  Qed.

  #[projections(primitive)] Record Split@{i} {Γ} {wfΓ} (A : PSh@{i} Γ wfΓ) : Type@{i} := {
    dtree :> DTree Γ;
    cover : forall (Δ : context) wfΔ ρ, overtree dtree Δ -> A Δ wfΔ ρ
  }.

  Arguments dtree {_ _ _}.
  Arguments cover {_ _ _}.

  (* Definition Split_PSh {Γ} : PSh Γ -> PSh Γ:=
   fun A Δ ρ => Split (PSh_PSh ρ A). *)

  Lemma split_hom_PSh {Γ wfΓ} {A B : PSh Γ wfΓ} : hom A B -> Split A -> Split B.
  Proof.
    intros hhom hA.
    destruct hA as [dA hA].
    exists dA.
    intros Δ wfΔ ρ odA.
    apply hhom.
    now apply hA.
  Qed.

  Lemma Split_wkn {Γ wfΓ} {A : PSh Γ wfΓ} : Split A ->
    forall {Δ wfΔ} ρ, Split (wfΓ := wfΔ) (fun Ξ wfΞ (ρ' : Ξ ≤ Δ) => A Ξ wfΞ (ρ'∘w ρ)).
  Proof.
    intros hA Δ wfΔ ρ.
    exists (DTree_PSh Δ hA.(dtree)).
    intros Ξ wfΞ σ Hover.
    apply hA.
    now eapply over_DTree_PSh.
  Defined.

  Lemma Split_wkn_inv {Γ wfΓ A} : (forall Δ wfΔ (ρ : Δ ≤ Γ), Split (wfΓ:=wfΔ) (fun Ξ wfΞ ρ' => A Ξ wfΞ (ρ'∘w ρ))) ->
    Split (wfΓ:=wfΓ) A.
  Proof.
    intros hA.
    specialize (hA Γ wfΓ wk_id).
    eapply split_hom_PSh.
    2: apply hA.
    intros Δ wfΔ ρ a.
    refine (PSh_rew A _ _ _ a).
    apply wfΓ.
    bsimpl.
    reflexivity.
  Qed.

  Definition shf {Γ} wfΓ (A : PSh Γ wfΓ) := forall Δ wfΔ (ρ : Δ ≤ Γ) new,
      A (Δ,,new↦true) (wfc_consF wfΔ) (wk_Fstep _ _ ρ) ->
      A (Δ,,new↦false) (wfc_consF wfΔ) (wk_Fstep _ _ ρ) ->
      A Δ wfΔ ρ.

  Lemma shf_PSh {Γ wfΓ A} : shf wfΓ A -> forall {Δ wfΔ} {ρ : Δ ≤ Γ}, shf wfΔ (PSh_PSh wfΔ ρ A).
  Proof.
    intros hAshf ??? Ξ wfΞ ρΞ new hAt hAf.
    unfold PSh_PSh, shf in *.
    now eapply hAshf.
  Qed.

  Lemma Split_shf {Γ wfΓ} {A : PSh Γ wfΓ} : shf wfΓ (fun Δ wfΔ ρ => Split (wfΓ:=wfΔ) (fun Ξ wfΞ ρ' => A Ξ wfΞ (ρ'∘w ρ))).
  Proof.
    intros Δ wfΔ ρ new [dAt hAt] [dAf hAf].
    exists (node dAt dAf).
    intros Ξ wfΞ ρΞ hover.
    cbn in hover.
    destruct (decide_in Ξ new) as [[] hin|hnotin].
    - specialize (hAt Ξ wfΞ (wk_new new true ρΞ hin) hover).
      refine (PSh_rew A _ _ _ hAt).
      bsimpl. reflexivity.
    - specialize (hAf Ξ wfΞ (wk_new new false ρΞ hin) hover).
      refine (PSh_rew A _ _ _ hAf).
      bsimpl. reflexivity.
    - destruct hover.
  Qed.



Definition over {Γ : context} {wfΓ} (d : DTree Γ) (A: PSh Γ wfΓ) := forall Δ wfΔ (ρ : Δ ≤ Γ), overtree d Δ -> A Δ wfΔ ρ.


Lemma over_PSh {Γ: context} {wfΓ} {d : DTree Γ} {A: PSh Γ wfΓ} : over d A ->
  forall Δ wfΔ (ρ : Δ ≤ Γ) (d' : DTree Δ), (forall Ξ (wfΞ : [|-Ξ]) (ρ' : Ξ ≤ Δ), overtree d' Ξ -> overtree d Ξ) -> over d' (PSh_PSh wfΔ ρ A).
Proof.
  intros od ???? hdd' Ξ wfΞ ρΞ od'.
  now apply od.
Qed.

Lemma over_new : forall {Γ wfΓ} (A : PSh Γ wfΓ) {new} (b:bool) {dt df}, over (node dt df) A ->
  over (Γ:=Γ,,new↦b) (if b return _ then dt else df) (PSh_PSh (wfc_consF wfΓ) (wk_Fstep new b wk_id) A).
Proof.
  intros * hA.
  eapply over_PSh; [apply hA|].
  intros Δ wfΔ ρ hover.
  cbn.
  rewrite (decide_in_in _  new b (Fwk ρ new b (in_hereF _ new b))).
  now destruct b.
Qed.

Lemma Split_bind_alg@{i j} : forall {Γ wfΓ} {A B: PSh Γ wfΓ},
  shf@{j} wfΓ B -> forall (hA : Split@{i} A),
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> B Δ wfΔ ρ)->
  forall Δ wfΔ (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
  intros [Γ L] wfΓ A B hBshf [dA hA] hB; cbn in *.
  induction dA as [L |L new dt ihAt df ihAf].
  - intros Δ wfΔ ρ; cbn in *.
    apply hB, ρ.
  - change L with (Fctx (Build_context Γ L)) in new.
    specialize (ihAt (wfc_consF wfΓ) (PSh_PSh (wfc_consF wfΓ) (wk_Fstep new true wk_id) A)
      (PSh_PSh (wfc_consF wfΓ) (wk_Fstep new true wk_id) B) (shf_PSh hBshf)
      (over_new A true hA) (over_new B true hB)).
    specialize (ihAf (wfc_consF wfΓ) (PSh_PSh (wfc_consF wfΓ) (wk_Fstep new false wk_id) A)
      (PSh_PSh (wfc_consF wfΓ) (wk_Fstep new false wk_id) B) (shf_PSh hBshf)
      (over_new A false hA) (over_new B false hB)).
    intros Δ wfΔ ρ.
    destruct (decide_in Δ new) as [[] hin|hnotin].
    + specialize (ihAt Δ wfΔ (wk_new new true ρ hin)).
      refine (PSh_rew B _ ρ _ ihAt).
      bsimpl; reflexivity.
    + specialize (ihAf Δ wfΔ (wk_new new false ρ hin)).
      refine (PSh_rew B _ ρ _ ihAf).
      bsimpl; reflexivity.
    + set (new' := Build_newnat Δ new hnotin).
      eapply hBshf.
      * specialize (ihAt (Δ,, new' ↦ true) (wfc_consF wfΔ) (wk_Fup true ρ new new' eq_refl)).
        refine (PSh_rew B _ _ _ ihAt).
        bsimpl. reflexivity.
      * specialize (ihAf (Δ,, new' ↦ false) (wfc_consF wfΔ) (wk_Fup false ρ new new' eq_refl)).
        refine (PSh_rew B _ _ _ ihAf).
        bsimpl. reflexivity.
Qed.

(* Lemma Split_bind_alg : forall {Γ} {A B: PSh Γ},
  shf B ->
  hom A B ->
  Split A -> (forall Δ (ρ : Δ ≤ Γ), B Δ ρ).
Proof.
  intros Γ A B hB hhom hA ??.
  eapply (Split_bind_alg_over hB hA); clear Δ ρ.
  intros ?? hoverA.
  eapply hhom.
  now eapply hA.
Qed. *)

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

Lemma Split_return : forall {Γ wfΓ} {A: PSh Γ wfΓ}, (forall Δ wfΔ ρ, A Δ wfΔ ρ) -> Split A.
Proof.
  intros Γ wfΓ A hA.
  exists (leaf Γ).
  easy.
Qed.


Lemma Split_Splitfree {Γ wfΓ} {A : PSh Γ wfΓ} : Split A -> Split (wfΓ := wfΓ) (fun Δ wfΔ ρ => forall Ξ wfΞ ρ', A Ξ wfΞ (ρ'∘w ρ)).
Proof.
  intros * hA.
  exists hA.(dtree).
  intros ? wfΔ ? hover *.
  apply hA.(cover).
  now apply overtree_PSh. Show Proof.
Defined.

Lemma Split_Splitfree_inv {Γ wfΓ} {A : PSh Γ wfΓ} : Split (wfΓ:=wfΓ) (fun Δ wfΔ ρ => forall Ξ wfΞ ρ', A Ξ wfΞ (ρ'∘w ρ)) -> Split A.
Proof.
  intros hA.
  exists hA.(dtree).
  intros * ohA *.
  rewrite <- wk_comp_lunit.
  now apply hA.
Defined.

Lemma Split_bind: forall {Γ wfΓ} {A B : PSh Γ wfΓ} (hA :Split A),
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ -> Split (wfΓ:=wfΔ) (fun Ξ wfΞ ρ' => B Ξ wfΞ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros ????? hB.
  apply Split_wkn_inv.
  unshelve eapply (Split_bind_alg Split_shf).
  2: apply (Split_Splitfree hA).
  intros ??? ohA.
  now apply hB.
Qed.

Lemma Split_wk_bind : forall {Γ wfΓ} {A : PSh Γ wfΓ} (hA : Split A),
  forall {Δ wfΔ} (ρ : Δ ≤ Γ) {B : PSh Δ wfΔ},
    (forall Ξ wfΞ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> Split (wfΓ := wfΞ) (fun Θ wfΘ (ρ'' : Θ ≤ Ξ) => B Θ wfΘ (ρ''∘w ρ'))) ->
    Split B.
Proof.
  intros ???????? hB.
  set (hA' := Split_wkn (wfΔ := wfΔ) hA ρ).
  unshelve eapply Split_bind.
  2: apply hA'.
  intros Ξ wfΞ ρ' ohA'.
  apply hB.
  now eapply over_DTree_PSh.
Qed.

Lemma Split_wk_bind_return : forall {Γ wfΓ} {A : PSh Γ wfΓ} (hA : Split A),
  forall {Δ wfΔ} (ρ : Δ ≤ Γ) {B : PSh Δ wfΔ}, (forall Ξ wfΞ (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> B Ξ wfΞ ρ') -> Split B.
Proof.
  intros ???????? hB.
  eapply (Split_wk_bind hA ρ).
  intros ??? ohA.
  eapply Split_return.
  intros Θ wfΘ ρΘ.
  eapply hB.
  now eapply overtree_PSh.
Qed.

Lemma Split_bind_return: forall {Γ wfΓ} {A B : PSh Γ wfΓ} (hA :Split A),
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ ->  B Δ wfΔ ρ) ->
  Split B.
Proof.
  intros ????? hB.
  eapply (Split_bind hA).
  intros ??? ohA.
  apply Split_return.
  intros Ξ wfΞ ρΞ.
  apply hB.
  now eapply overtree_PSh.
Qed.


Definition dover {Γ wfΓ} {A : PSh Γ wfΓ} (hA : Split A) (P : forall Δ wfΔ ρ, A Δ wfΔ ρ -> Type)
  := forall Δ wfΔ (ρ : Δ ≤ Γ) (ohA : overtree hA Δ),
  P Δ wfΔ ρ (cover hA Δ wfΔ ρ ohA).

Definition dover_PSh {Γ wfΓ} {A : PSh Γ wfΓ} {P} {hA : Split A}: dover hA P -> forall {Δ} {wfΔ} {ρ : Δ ≤ Γ},
  dover (wfΓ := wfΔ) (Split_wkn hA ρ) (fun Ξ wfΞ ρ' => P Ξ wfΞ (ρ'∘w ρ)).
Proof.
  intros hP ??? Ξ wfΞ ρΞ ohA.
  apply hP.
Qed.

Definition dover_apply {Γ wfΓ} {A : PSh Γ wfΓ} {P Q: forall Δ wfΔ ρ, A Δ wfΔ ρ -> Type} {hA : Split A} :
  (forall Δ wfΔ ρ a, P Δ wfΔ ρ a -> Q Δ wfΔ ρ a) -> dover hA P-> dover hA Q:=
 (fun f hP Δ wfΔ ρ ohA => f Δ wfΔ ρ _ (hP _ _ _ _)).
(* 
Definition ddover@{i j k} {Γ wfΓ} {A : PSh@{i} Γ wfΓ} 
  {P: forall Δ wfΔ ρ, A Δ wfΔ ρ -> Type@{j}} (Q : forall Δ wfΔ ρ a, P Δ wfΔ ρ a -> Type@{k}) {hA : Split A} :
  dover hA P -> Type@{k} :=
 (fun hP => forall Δ wfΔ ρ ohA, Q Δ wfΔ ρ _ (hP _ _ _ ohA)). *)

Definition dSplit {Γ wfΓ} {A : PSh Γ wfΓ} (P : forall Δ wfΔ ρ, A Δ wfΔ ρ -> Type) (hA : Split A) :=
  Split (wfΓ := wfΓ) (fun Δ wfΔ (ρ : Δ ≤ Γ) => forall (ohA : overtree hA Δ), P Δ wfΔ ρ (hA.(cover) Δ wfΔ ρ ohA)).


Lemma dSplit_bind_alg : forall {Γ wfΓ} {A B: PSh Γ wfΓ} {P},
  shf wfΓ B -> forall {hA : Split A} (hP : dSplit P hA),
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ -> B Δ wfΔ ρ)->
  forall Δ wfΔ (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
  intros ????? hshf ?? hB.
  eapply (Split_bind_alg hshf hA).
  intros Δ wfΔ ρ ohA.
  eapply PSh_root.
  eapply (Split_bind_alg (shf_PSh hshf) (Split_wkn hP ρ)).
  intros Ξ wfΞ ρΞ hoverP.
  eapply hB.
  now eapply overtree_PSh.
  now eapply over_DTree_PSh.
  Unshelve. tea.
Qed.

(* Lemma dSplit_solve : forall Γ wfΓ (A B : PSh Γ)
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
Qed. *)

Lemma Split_assoc {Γ Δ Ξ wfΓ wfΞ} {ρ : Δ ≤ Γ} {ρ' : Ξ ≤ Δ} {A : PSh Γ wfΓ} :
  Split (wfΓ:= wfΞ) (fun Θ wfΘ ρ'' => A Θ wfΘ (ρ'' ∘w (ρ'∘w ρ))) ->
  Split (wfΓ := wfΞ) (fun Θ wfΘ ρ'' => A Θ wfΘ ((ρ'' ∘w ρ')∘w ρ)).
Proof.
  intros hA.
  exists hA.(dtree).
  intros Ω wfΩ ρΩ ohA.
  rewrite wk_comp_assoc.
  now apply hA.(cover).
Qed.

Lemma dSplit_bind {Γ wfΓ} {A B : PSh Γ wfΓ} {P : forall Δ wfΔ (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ -> Split (wfΓ := wfΔ) (fun Ξ wfΞ ρ' => B Ξ wfΞ (ρ' ∘w ρ))) ->
  Split B.
Proof.
  intros hB.
  eapply (Split_bind hA).
  intros ??? ohA.
  apply (Split_wk_bind hP ρ).
  intros Ξ wfΞ ρ' ohP.
  eapply Split_assoc.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

Lemma dSplit_bind_return {Γ wfΓ} {A B : PSh Γ wfΓ} {P : forall Δ wfΔ (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ wfΔ (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ -> B Δ wfΔ ρ) ->
  Split B.
Proof.
  intros hB.
  eapply (dSplit_bind hP).
  intros ??? ohA ohP.
  eapply Split_return.
  intros Ξ wfΞ ρΞ.
  eapply hB.
  all: now eapply overtree_PSh.
Qed.

Lemma dSplit_wkn : forall {Γ wfΓ} {A : PSh Γ wfΓ} {P : forall Δ wfΔ (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type} {hA : Split A}, dSplit P hA ->
  forall {Δ wfΔ} (ρ : Δ ≤ Γ), dSplit (wfΓ := wfΔ) (fun Ξ wfΞ ρ' a=> P Ξ wfΞ (ρ'∘w ρ) a) (Split_wkn hA ρ).
Proof.
  intros ????? hP ???.
  exists (DTree_PSh Δ hP.(dtree)).
  intros Ξ wfΞ ρΞ ohP ohA.
  eapply hP.(cover).
  now eapply over_DTree_PSh.
Defined.

Lemma dSplit_wk_bind {Γ wfΓ} {A : PSh Γ wfΓ} {P : forall Δ wfΔ (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ wfΔ} (ρ : Δ ≤ Γ) (B : PSh Δ wfΔ),
    (forall Ξ wfΞ (ρ' : Ξ ≤ Δ), overtree hA Ξ -> overtree hP Ξ -> Split (wfΓ:= wfΞ) (fun Θ wfΘ (ρ'' : Θ ≤ Ξ) => B Θ wfΘ (ρ'' ∘w ρ'))) ->
    Split B.
Proof.
  intros ???? hB.
  eapply (dSplit_bind (dSplit_wkn hP ρ)).
  intros Ξ wfΞ ρΞ ohA ohP.
  eapply hB.
  all: now eapply over_DTree_PSh.
Qed.

Lemma dSplit_wk_bind_return {Γ wfΓ} {A : PSh Γ wfΓ} {P : forall Δ wfΔ (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ wfΔ} (ρ : Δ ≤ Γ) (B : PSh Δ wfΔ),
  (forall Ξ wfΞ (ρ' : Ξ ≤ Δ), overtree hA Ξ -> overtree hP Ξ -> B Ξ wfΞ ρ') ->
  Split B.
Proof.
  intros ???? hB.
  eapply (dSplit_wk_bind hP ρ).
  intros ??? ohA ohP.
  eapply Split_return.
  intros Θ wfΘ ρΘ.
  eapply hB.
  all: now eapply overtree_PSh.
Qed.

End Sheaves.

Arguments dtree {_ _ _ _ _}.
Arguments cover {_ _ _ _ _}.



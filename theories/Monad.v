From LogRel Require Import Utils Syntax.All GenericTyping.

Inductive DTree (L : Fcontext) : Set :=
  | leaf : DTree L
  | node (new : newnat L):
    DTree (Fcons' L new true) ->
    DTree (Fcons' L new false) ->
    DTree L.


Arguments node {_ _}.

Fixpoint overtree0 {L} (d : DTree L) L' : SProp :=
  match d with
  | leaf _ => L' ≤ε L
  | @node _ new dt df =>
    match decide_in L' new with
    | is_in true _ => overtree0 dt L'
    | is_in false _ => overtree0 df L'
    | is_notin _ => SFalse
    end
  end.

Lemma overtree_Fwk {L L'} {d : DTree L} : overtree0 d L' -> L' ≤ε L.
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
  overtree0 (DTree_PSh L' d) L'' -> overtree0 d L''.
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
  overtree0 d L'' -> overtree0 (DTree_PSh L' d) L''.
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

Lemma overtree0_PSh {L L' L'' : Fcontext} {Fρ : L'' ≤ε L'} (d : DTree L) :
  overtree0 d L' -> overtree0 d L''.
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

Fixpoint DTree' (L : list Fcontext) : Set :=
  match L with nil => unit | cons F L' => prod (DTree F) (DTree' L') end.

Fixpoint overtree' {L : list Fcontext } {L' ρε} (wρε  : well_Fweakening ρε L' L) {struct wρε}: DTree' L -> SProp :=
  match wρε with
  | well_emptyF => fun _ => Logic.StrictProp.sUnit
  | well_stepF _ _  wρε => fun d => overtree' wρε d
  | well_upF _ _ _ wρ ρF => fun d => match d with pair d ds => SAnd (overtree0 d F') overtree' wρ ds end
  end.

Local Set Universe Polymorphism.
Section Sheaves.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta} `{!WfContextProperties}.


  Definition PSh@{i} Γ : Type@{i+1} := forall (Δ : context), [|-Δ] -> Δ ≤ Γ -> Type@{i}.
  Definition dPSh@{i j} Γ (A : PSh@{i} Γ) := forall (Δ : context) (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), A Δ wfΔ ρ -> Type@{j}.

  Definition PSh_PSh {Γ Δ} (ρ : Δ ≤ Γ): PSh Γ -> PSh Δ :=
    fun A Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ ∘w ρ).

  Lemma PSh_rew {Γ} (A : PSh Γ) : forall {Δ} wfΔ (ρ ρ' : Δ ≤ Γ), ρ =1 ρ' -> A Δ wfΔ ρ -> A Δ wfΔ ρ'.
  Proof.
    intros ???? heq1 hA.
    apply wk_to_ren_inj in heq1.
    now destruct heq1.
  Qed.

  Lemma PSh_root {Γ Δ wfΔ ρ} {A : PSh Γ}: (forall Ξ wfΞ (ρΞ : Ξ ≤ Δ), A Ξ wfΞ (ρΞ∘w ρ))
    -> A Δ wfΔ ρ.
  Proof.
    intros hA.
    rewrite <- wk_comp_lunit.
    eapply hA.
  Qed.

  Lemma PSh_wkn_inv {Γ Δ ρ} (wfΔ : [|-Δ]) {A : PSh Γ}: (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), A Ξ wfΞ (ρΞ∘w ρ))
    -> A Δ wfΔ ρ.
  Proof.
    intros hA.
    rewrite <- wk_comp_lunit.
    now eapply hA.
  Qed.

  Definition hom {Γ} (A B : PSh Γ) := forall Δ wfΔ ρ, A Δ wfΔ ρ -> B Δ wfΔ ρ.

  Lemma hom_PSh {Γ} {A B : PSh Γ} : hom A B -> forall {Δ} {ρ : Δ ≤ Γ}, hom (PSh_PSh ρ A) (PSh_PSh ρ B).
  Proof.
    intros hhom ?? Ξ ρΞ hA.
    apply hhom.
  Qed.

  #[projections(primitive)] Record Split@{i} {Γ} (A : PSh@{i} Γ) : Type@{i} := {
    wfc_Split : [|-Γ];
    dtree :> DTree Γ;
    cover : forall (Δ : context) (wfΔ : [|-Δ]) ρ, overtree dtree Δ -> A Δ wfΔ ρ
  }.

  Arguments Build_Split {_ _}.
  Arguments wfc_Split {_ _}.
  Arguments dtree {_ _}.
  Arguments cover {_ _}.

  (* Definition Split_PSh {Γ} : PSh Γ -> PSh Γ:=
   fun A Δ ρ => Split (PSh_PSh ρ A). *)

  Lemma Split_hom_PSh {Γ} {A B : PSh Γ} : hom A B -> Split A -> Split B.
  Proof.
    intros hhom hA.
    refine (Build_Split hA.(wfc_Split) hA _).
    intros Δ wfΔ ρ odA.
    apply hhom.
    now apply hA.
  Qed.

  Lemma Split_wkn {Γ} {A : PSh Γ} : Split A ->
    forall {Δ} (wfΔ : [|-Δ]) ρ, Split (fun Ξ wfΞ (ρΞ : Ξ ≤ Δ) => A Ξ wfΞ (ρΞ∘w ρ)).
  Proof.
    intros hA Δ wfΔ ρ.
    refine (Build_Split wfΔ (DTree_PSh Δ hA) _).
    intros Ξ wfΞ ρΞ ohA.
    apply hA; tea.
    now eapply over_DTree_PSh.
  Defined.

  Lemma Split_wkn_inv {Γ} {wfΓ : [|-Γ]} {A : PSh Γ} :
    (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), Split (fun Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ∘w ρ))) ->
    Split A.
  Proof.
    intros hA.
    specialize (hA Γ wfΓ wk_id).
    eapply Split_hom_PSh.
    2: apply hA.
    intros Δ wfΔ ρ a.
    refine (PSh_rew A _ _ _ _ a).
    bsimpl.
    reflexivity.
  Qed.

  Definition shf {Γ} (A : PSh Γ) := forall Δ wfΔ (ρ : Δ ≤ Γ) new,
      A (Δ,,new↦true) (wfc_consF wfΔ) (wk_Fstep _ _ ρ) ->
      A (Δ,,new↦false) (wfc_consF wfΔ) (wk_Fstep _ _ ρ) ->
      A Δ wfΔ ρ.

  Lemma shf_PSh {Γ A} : shf A -> forall {Δ} {ρ : Δ ≤ Γ}, shf (PSh_PSh ρ A).
  Proof.
    intros hAshf ?? Ξ wfΞ ρΞ new hAt hAf.
    unfold PSh_PSh, shf in *.
    now eapply hAshf.
  Qed.

  Lemma Split_shf {Γ} {A : PSh Γ} : shf (fun Δ wfΔ ρ => Split (fun Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ ∘w ρ))).
  Proof.
    intros Δ wfΔ ρ new [wft dAt hAt] [wff dAf hAf].
    refine (Build_Split wfΔ (node dAt dAf) _).
    intros Ξ wfΞ ρΞ oA.
    cbn in oA.
    destruct (decide_in Ξ new) as [[] hin|hnotin].
    - specialize (hAt Ξ wfΞ (wk_new new true ρΞ hin) oA).
      refine (PSh_rew A _ _ _ _ hAt).
      bsimpl. reflexivity.
    - specialize (hAf Ξ wfΞ (wk_new new false ρΞ hin) oA).
      refine (PSh_rew A _ _ _ _ hAf).
      bsimpl. reflexivity.
    - destruct oA.
  Qed.



Definition over {Γ : context} (d : DTree Γ) (A: PSh Γ) :=
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree d Δ -> A Δ wfΔ ρ.


Lemma over_PSh {Γ: context} {d : DTree Γ} {A: PSh Γ} : over d A ->
  forall Δ (ρ : Δ ≤ Γ) (d' : DTree Δ),
    (forall Ξ (wfΞ : [|-Ξ]) (ρ' : Ξ ≤ Δ), overtree d' Ξ -> overtree d Ξ) ->
    over d' (PSh_PSh ρ A).
Proof.
  intros od ??? hdd' Ξ wfΞ ρΞ od'.
  now apply od.
Qed.

Lemma over_new : forall {Γ} (A : PSh Γ) {new} (b:bool) {dt df}, over (node dt df) A ->
  over (Γ:=Γ,,new↦b) (if b return _ then dt else df) (PSh_PSh (wk_Fstep new b wk_id) A).
Proof.
  intros * hA.
  eapply over_PSh; [apply hA|].
  intros Δ wfΔ ρ hover.
  cbn.
  rewrite (decide_in_in _  new b (Fwk ρ new b (in_hereF _ new b))).
  now destruct b.
Qed.

Lemma Split_bind_alg@{i j} : forall {Γ} {A : PSh@{i} Γ} {B: PSh@{j} Γ},
  shf@{j} B -> forall (hA : Split@{i} A),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA Δ -> B Δ wfΔ ρ)->
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
  intros [Γ L] ?? hBshf [wfΓ dA hA] hB; cbn in *.
  induction dA as [L |L new dt ihAt df ihAf].
  - intros Δ wfΔ ρ; cbn in *.
    now apply hB, ρ.
  - change L with (Fctx (Build_context Γ L)) in new.
    specialize (ihAt (PSh_PSh (wk_Fstep new true wk_id) A)
      (PSh_PSh (wk_Fstep new true wk_id) B)
      (shf_PSh hBshf) (wfc_consF wfΓ)
      (over_new A true hA) (over_new B true hB)).
    specialize (ihAf (PSh_PSh (wk_Fstep new false wk_id) A)
      (PSh_PSh (wk_Fstep new false wk_id) B)
      (shf_PSh hBshf) (wfc_consF wfΓ)
      (over_new A false hA) (over_new B false hB)).
    intros Δ wfΔ ρ.
    destruct (decide_in Δ new) as [[] hin|hnotin].
    + specialize (ihAt Δ wfΔ (wk_new new true ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAt).
      bsimpl; reflexivity.
    + specialize (ihAf Δ wfΔ (wk_new new false ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAf).
      bsimpl; reflexivity.
    + set (new' := Build_newnat Δ new hnotin).
      eapply hBshf; tea.
      * specialize (ihAt (Δ,, new' ↦ true) (wfc_consF wfΔ) (wk_Fup true ρ new new' eq_refl)).
        refine (PSh_rew B _ _ _ _ ihAt).
        bsimpl. reflexivity.
      * specialize (ihAf (Δ,, new' ↦ false) (wfc_consF wfΔ) (wk_Fup false ρ new new' eq_refl)).
        refine (PSh_rew B _ _ _ _ ihAf).
        bsimpl. reflexivity.
Qed.



Lemma Split_return {Γ} (wfΓ : [|-Γ]) {A: PSh Γ} :
  (forall Δ (wfΔ : [|-Δ]) ρ, A Δ  wfΔ ρ) -> Split A.
Proof.
  intros hA.
  refine (Build_Split wfΓ (leaf Γ) _).
  easy.
Qed.


Lemma Split_Splitfree {Γ} {A : PSh Γ} :
  Split A -> Split (fun Δ wfΔ ρ => forall Ξ (wfΞ : [|-Ξ]) ρΞ, A Ξ wfΞ (ρΞ∘w ρ)).
Proof.
  intros * hA.
  refine (Build_Split hA.(wfc_Split) hA.(dtree) _).
  intros ? wfΔ ? ohA ???.
  apply hA.(cover); tea.
  now apply overtree_PSh.
Defined.

Lemma Split_Splitfree_inv {Γ} {A : PSh Γ} :
  Split (fun Δ wfΔ ρ => forall Ξ (wfΞ : [|-Ξ]) ρΞ, A Ξ wfΞ (ρΞ∘w ρ)) -> Split A.
Proof.
  intros hA.
  refine (Build_Split hA.(wfc_Split) hA.(dtree) _).
  intros ??? ohA *.
  rewrite <- wk_comp_lunit.
  now apply hA.
Defined.

Lemma Split_bind {Γ} {A : PSh Γ} {B : PSh Γ} (hA :Split A):
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ ->
    Split (fun Ξ wfΞ ρΞ => B Ξ wfΞ (ρΞ ∘w ρ))) ->
  Split B.
Proof.
  intros hB.
  unshelve eapply Split_wkn_inv.
  1: eapply hA.
  unshelve eapply (Split_bind_alg Split_shf).
  2: apply (Split_Splitfree hA). 
  intros ??? ohA.
  now apply hB.
Qed.

Lemma Split_bind_return: forall {Γ} {A B : PSh Γ} (hA :Split A),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA.(dtree) Δ ->  B Δ wfΔ ρ) ->
  Split B.
Proof.
  intros ???? hB.
  assert (wfΓ : [|-Γ]) by apply hA.
  now exists hA.
Qed.

Lemma Split_wk_bind : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) {B : PSh Δ},
    (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA.(dtree) Ξ ->
      Split (fun Θ wfΘ (ρΘ : Θ ≤ Ξ) => B Θ wfΘ (ρΘ∘w ρΞ))) ->
    Split B.
Proof.
  intros ??????? hB.
  set (hA' := Split_wkn hA wfΔ ρ).
  unshelve eapply Split_bind.
  2: apply hA'.
  intros Ξ wfΞ ρΞ ohA'.
  apply hB; tea.
  now eapply over_DTree_PSh.
Qed.

Lemma Split_wk_bind_return : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) {B : PSh Δ},
  (forall Ξ (wfΞ : [|-Ξ]) (ρ' : Ξ ≤ Δ), overtree hA.(dtree) Ξ -> B Ξ wfΞ ρ') ->
  Split B.
Proof.
  intros ??????? hB.
  refine (Build_Split wfΔ (DTree_PSh Δ hA) _).
  intros Ξ wfΞ ρΞ ohA.
  eapply hB; tea.
  now eapply over_DTree_PSh.
Qed.


Definition dover {Γ} {A : PSh Γ} (hA : Split A) (P : dPSh Γ A)
  := forall Δ wfΔ (ρ : Δ ≤ Γ) (ohA : overtree hA Δ),
  P Δ wfΔ ρ (cover hA Δ wfΔ ρ ohA).

Definition dover_PSh {Γ} {A : PSh Γ} {P} {hA : Split A}: dover hA P ->
  forall {Δ} {wfΔ} {ρ : Δ ≤ Γ},
    dover (Split_wkn hA wfΔ ρ) (fun Ξ wfΞ ρΞ => P Ξ wfΞ (ρΞ ∘w ρ)).
Proof.
  intros hP ??? Ξ wfΞ ρΞ ohA.
  apply hP.
Qed.

Definition dover_apply {Γ} {A : PSh Γ}
  {P Q: dPSh Γ A} {hA : Split A} :
  (forall Δ (wfΔ : [|-Δ]) ρ a, P Δ wfΔ ρ a -> Q Δ wfΔ ρ a) -> dover hA P-> dover hA Q:=
 (fun f hP Δ wfΔ ρ ohA => f Δ wfΔ ρ _ (hP _ _ _ _)).


Definition dSplit {Γ} {A : PSh Γ} (P : dPSh Γ A)
  (hA : Split A) :=
  Split (fun Δ wfΔ (ρ : Δ ≤ Γ) =>
    forall (ohA : overtree hA Δ), P Δ wfΔ ρ (hA.(cover) Δ wfΔ ρ ohA)).


Lemma dSplit_bind_alg : forall {Γ} {A B: PSh Γ} {P},
  shf B -> forall {hA : Split A} (hP : dSplit P hA),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ -> B Δ wfΔ ρ)->
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
  intros ???? hshf ?? hB.
  eapply (Split_bind_alg hshf hA).
  intros Δ wfΔ ρ ohA.
  eapply PSh_wkn_inv; tea.
  eapply (Split_bind_alg (shf_PSh hshf) (Split_wkn hP wfΔ ρ)).
  intros Ξ wfΞ ρΞ ohP.
  eapply hB; tea.
  now eapply overtree_PSh.
  now eapply over_DTree_PSh.
Qed.


Lemma Split_assoc {Γ Δ Ξ} {ρ : Δ ≤ Γ} {ρΞ : Ξ ≤ Δ} {A : PSh Γ} :
  Split (fun Θ wfΘ ρΘ => A Θ wfΘ (ρΘ ∘w (ρΞ ∘w ρ))) ->
  Split (fun Θ wfΘ ρΘ => A Θ wfΘ ((ρΘ ∘w ρΞ) ∘w ρ)).
Proof.
  eapply Split_hom_PSh.
  intros Θ wfΘ hA.
  now rewrite wk_comp_assoc.
Qed.

Lemma dSplit_bind {Γ}
  {A : PSh Γ} {B : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ ->
    Split (fun Ξ wfΞ ρΞ => B Ξ wfΞ (ρΞ ∘w ρ))) ->
  Split B.
Proof.
  intros hB.
  eapply (Split_bind hA).
  intros ??? ohA.
  eapply (Split_wk_bind hP wfΔ ρ). tea.
  intros Ξ wfΞ ρ' ohP.
  eapply Split_assoc.
  eapply hB; tea.
  now eapply overtree_PSh.
Qed.

Lemma dSplit_bind_return {Γ}
  {A : PSh Γ} {B : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA Δ -> overtree hP Δ -> B Δ wfΔ ρ) ->
  Split B.
Proof.
  intros hB.
  unshelve eapply (dSplit_bind hP); tea.
  intros ??? ohA ohP.
  eapply Split_return; tea.
  intros Ξ wfΞ ρΞ.
  eapply hB; tea.
  all: now eapply overtree_PSh.
Qed.

Lemma dSplit_wkn {Γ}
  {A : PSh Γ} {P : dPSh Γ A} :
  forall {hA : Split A}, dSplit P hA ->
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ),
    dSplit (fun Ξ wfΞ ρΞ a=> P Ξ wfΞ (ρΞ∘w ρ) a) (Split_wkn hA wfΔ ρ).
Proof.
  intros ? hP ???.
  refine (Build_Split wfΔ (DTree_PSh Δ hP.(dtree)) _).
  intros Ξ wfΞ ρΞ ohP ohA.
  eapply hP; tea.
  now eapply over_DTree_PSh.
Defined.

Lemma dSplit_wk_bind {Γ} {A : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) (B : PSh Δ),
    (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA Ξ ->
      overtree hP Ξ -> Split (fun Θ wfΘ (ρΘ : Θ ≤ Ξ) => B Θ wfΘ (ρΘ ∘w ρΞ))) ->
    Split B.
Proof.
  intros ???? hB.
  eapply (dSplit_bind (dSplit_wkn hP wfΔ ρ)).
  intros Ξ wfΞ ρΞ ohA ohP.
  eapply hB; tea.
  all: now eapply over_DTree_PSh.
Qed.

Lemma dSplit_wk_bind_return {Γ} {A : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) (B : PSh Δ),
  (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA Ξ -> overtree hP Ξ -> B Ξ wfΞ ρΞ) ->
  Split B.
Proof.
  intros ???? hB.
  unshelve eapply (dSplit_wk_bind hP wfΔ ρ).
  intros ??? ohA ohP.
  eapply Split_return; tea.
  intros Θ wfΘ ρΘ.
  eapply hB; tea.
  all: now eapply overtree_PSh.
Qed.

End Sheaves.

Arguments Build_Split {_ _ _ _}.
Arguments wfc_Split {_ _ _ _}.
Arguments dtree {_ _ _ _}.
Arguments cover {_ _ _ _}.



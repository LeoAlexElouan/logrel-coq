From LogRel Require Import Utils Syntax.All GenericTyping.
From Equations Require Import Equations.

Inductive DTree (L : list Fcontext) : Set :=
  | leaf : DTree L 
  | node (i : list_index L) (new : newnat (list_at L i)):
    DTree (Fcons L i new true) ->
    DTree (Fcons L i new false) ->
    DTree L.
Derive NoConfusion EqDec for DTree.



Definition overtree0 L (d : DTree L) : SProp :=
  match d with
  | leaf _ => STrue
  | @node _ i new dt df => SFalse
(*     match decide_in L' n with
    | is_in true _ => overtree0 dt L'
    | is_in false _ => overtree0 df L'
    | is_notin _ => SFalse
    end *)
  end.

Fixpoint DTree_PSh {L L' ρε} (wρε : well_Fweakening ρε L' L)
  (d : DTree L) {struct d} : DTree L'.
Proof.
  destruct d as [| i new dt df].
  - apply leaf.
  - destruct (decide_in (list_at L' (ren_index wρε i)) new) as [b hin |hnotin].
    + refine (DTree_PSh (Fcons L i new b) L' _ _
        (match b with true=>dt|false=>df end)).
      now eapply εwk_new.
    + refine (@node _ (ren_index wρε i) (Build_newnat _ new hnotin) _ _).
      * unshelve eapply (DTree_PSh _ _ _ _ dt).
        2: now eapply εwk_Fup.
      * unshelve eapply (DTree_PSh _ _ _ _ df).
        2: now eapply εwk_Fup.
Defined.

Definition overtree {L L' ρε} (d : DTree L) (wρε : well_Fweakening ρε L' L) :=
  overtree0 L' (DTree_PSh wρε d).

(* Lemma f_equal_forhere A (P: A -> Type) (Q R :forall a, P a -> Type)
  B (f : forall a (p :P a), Q a p -> R a b -> B) a a' p p' q q' r r' (ea : a = a')
  (ep eq_rect _ P p _ ea = p' -> eq_rect _ Q q _ ea = q' -> f a p q = f a' p' q'.
Proof. revert ea; now intros <- <- <-. Qed. *)

Lemma DTree_PSh_eq' {L L'} {ρε ρε' : Fweakening} wρε wρε' d d' : ρε = ρε' -> d = d' ->
  DTree_PSh (L:=L) (L':=L') (ρε := ρε) wρε d = DTree_PSh (ρε := ρε') wρε' d'.
Proof. intros <- <-; f_equal; eapply well_Fwk_irr. Qed.

Lemma DTree_PSh_eq {L L'} {ρε ρε' : Fweakening} wρε wρε' d d' : ρε =1 ρε' -> d = d' ->
  DTree_PSh (L:=L) (L':=L') (ρε := ρε) wρε d = DTree_PSh (ρε := ρε') wρε' d'.
Proof. intros e ed.
  eapply DTree_PSh_eq'; tea.
  now eapply wf_eq1_eq.
Qed.

Lemma DTree_PSh_compose {L L' L'' ρε ρε'} (d : DTree L)
  (wρε : well_Fweakening ρε L' L) (wρε' : well_Fweakening ρε' L'' L') :
  DTree_PSh wρε' (DTree_PSh wρε d) = DTree_PSh (well_Fwk_compose wρε' wρε) d.
Proof.
  induction d in L', L'', ρε, ρε',wρε, wρε' |-*.
  + cbn. reflexivity.
  + cbn.
    destruct (decide_in (list_at L' (ren_index wρε i)) new)
      as [b hin'|hnotin']; cbn in *.
    - unshelve erewrite (decide_in_in (list_at L'' (ren_index (well_Fwk_compose wρε' wρε) i)) new b _).
      1: rewrite ren_index_compose; now eapply well_Fwk_in.
      destruct b.
      * rewrite IHd1. now eapply DTree_PSh_eq.
      * rewrite IHd2. now eapply DTree_PSh_eq.
    - destruct (decide_in (list_at L'' (ren_index wρε' (ren_index wρε i))) new)
      as [b hin''|hnotin''],
        (decide_in (list_at L'' (ren_index (well_Fwk_compose wρε' wρε) i)) new)
      as [b0 hin''0|hnotin''0].
      * assert (b = b0) as <-
          by (rewrite ren_index_compose in hin''0; now eapply functionality).
        destruct b.
       -- cbn. rewrite IHd1. now eapply DTree_PSh_eq.
       -- cbn. rewrite IHd2. now eapply DTree_PSh_eq.
      * eassert SFalse as []
          by (rewrite ren_index_compose in hnotin''0; now eapply notin_is_not_in).
      * eassert SFalse as []
          by (rewrite ren_index_compose in hin''0; now eapply notin_is_not_in).
      * rewrite IHd1, IHd2.
        clear IHd1 IHd2.
        set (P:=(fun var => not_in_Fctx (list_at L'' var) new)).
        change hnotin'' with (eq_sind P
          hnotin''0 (ren_index_compose i wρε wρε')).
        clear hnotin''.
        match goal with
          |- node _ _ _ (DTree_PSh ?wρεt0 _) (DTree_PSh ?wρεf0 _) = 
            node _ _ _ (DTree_PSh ?wρεt1 _) (DTree_PSh ?wρεf1 _) =>
          set (wρεt:=wρεt0); set (wρεf:=wρεf0); set (wρεt':=wρεt1); set (wρεf':=wρεf1) end;
          clearbody wρεt wρεf wρεt' wρεf'.
        replace wρεf with match (ren_index_compose i wρε wρε') as e in _ = i'
          return well_Fweakening _ (Fcons _ i' (Build_newnat _ _ (eq_sind P _ e)) _) _ with
           eq_refl => wρεf' end by eapply well_Fwk_irr.
        replace wρεt with match (ren_index_compose i wρε wρε') as e in _ = i'
          return well_Fweakening _ (Fcons _ i' (Build_newnat _ _ (eq_sind P _ e)) _) _ with
           eq_refl => wρεt' end by eapply well_Fwk_irr.
        pattern (ren_index wρε' (ren_index wρε i)), (ren_index_compose i wρε wρε').
        match goal with |- ?A0 ?j ?e => refine (match e as e' in _ = j' return A0 j' e' with
          eq_refl => eq_refl end) end.
Qed.

(* Lemma overtree_Fwk {L L'} {d : DTree L} : overtree0 d L' -> L' ≤ε L.
Proof.
  induction d as [ | L new Lt iht Lf ihf] ; cbn ; intros H ; auto.
  destruct (decide_in L' new).
  - eapply Fwk_compose.
    destruct b.
    + now apply iht.
    + now apply ihf.
    + eapply Fwk_Fstep; apply Fwk_id. 
  - destruct H.
Qed. *)



Lemma overtree0_PSh {L L' ρε} (wρε  : well_Fweakening ρε L' L) (d : DTree L) :
  overtree0 L d -> overtree0 L' (DTree_PSh wρε d).
Proof.
  intros o0d.
  destruct d.
  - constructor.
  - destruct o0d.
Qed.

Lemma overtree_PSh {L L' L'' ρε ρε'}
  (wρε  : well_Fweakening ρε L' L) (wρε'  : well_Fweakening ρε' L'' L')
  (d : DTree L) : overtree d wρε -> overtree d (well_Fwk_compose wρε' wρε).
Proof.
  intros od.
  unfold overtree in *.
  rewrite <- DTree_PSh_compose.
  now eapply overtree0_PSh.
Qed.



Lemma over_DTree_PSh {L L' L'' ρε ρε'}
  (wρε  : well_Fweakening ρε L' L) (wρε'  : well_Fweakening ρε' L'' L')
  (d : DTree L) :
  overtree d (well_Fwk_compose wρε' wρε) ->
  overtree (DTree_PSh wρε d) wρε'.
Proof.
  intros od.
  unfold overtree in *.
  now rewrite DTree_PSh_compose.
Qed.

Lemma over_DTree_PSh_inv {L L' L'' ρε ρε'}
  (wρε  : well_Fweakening ρε L' L) (wρε' : well_Fweakening ρε' L'' L')
  (d : DTree L) :
  overtree (DTree_PSh wρε d) wρε' ->
  overtree d (well_Fwk_compose wρε' wρε).
Proof.
  intros od.
  unfold overtree in *.
  now rewrite <- DTree_PSh_compose.
Qed.

(* Lemma well_DTree_PSh {L L' ρε}
  (wρε  : well_Fweakening ρε L' L)
  (d : DTree) (wd : well_DTree L d) :
  well_DTree L' (DTree_PSh wρε d wd).
Proof.
  induction wρε in d, wd |-*.
  + constructor.
  + cbn. constructor.
    eapply IHwρε.
  + cbn.
    revert wρε IHwρε; induction wd using well_cons_inv; intros.
    cbn in *.
    constructor.
    eapply IHwρε.
Qed. *)

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

  Lemma PSh_rew {Γ} (A : PSh Γ) : forall {Δ} wfΔ (ρ ρ' : Δ ≤ Γ), ρ =₁ ρ' -> A Δ wfΔ ρ -> A Δ wfΔ ρ'.
  Proof.
    intros ???? heq hA.
    pose (wk_to_ren_inj _ _ _ _ heq) as e.
    now destruct e.
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
    cover : forall (Δ : context) (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree dtree ρ -> A Δ wfΔ ρ
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
    forall {Δ} (wfΔ : [|-Δ]) ρ, Split (fun Ξ wfΞ (ρΞ : Ξ ≤ Δ) => A Ξ wfΞ (ρΞ ∘w ρ)).
  Proof.
    intros hA Δ wfΔ ρ.
    refine (Build_Split wfΔ (DTree_PSh ρ hA) _).
    intros Ξ wfΞ ρΞ ohA.
    apply hA; tea.
    unfold overtree in *. cbn.
    now rewrite <- DTree_PSh_compose.
  Defined.

  Lemma Split_wkn_inv {Γ} {wfΓ : [|-Γ]} {A : PSh Γ} :
    (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), Split (fun Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ∘w ρ))) ->
    Split A.
  Proof.
    intros hA.
    specialize (hA Γ wfΓ wk_id).
    eapply Split_hom_PSh, hA.
    intros Δ wfΔ ρ a.
    refine (PSh_rew A _ _ _ _ a); eapply wk_comp_runit_pointwise.
  Qed.

  Definition shf {Γ} (A : PSh Γ) := forall Δ wfΔ (ρ : Δ ≤ Γ) i new,
      A (Δ,, i : new ↦ true) (wfc_consF wfΔ) (wk_Fstep _ _ _ ρ) ->
      A (Δ,, i : new ↦ false) (wfc_consF wfΔ) (wk_Fstep _ _ _ ρ) ->
      A Δ wfΔ ρ.

  Lemma shf_PSh {Γ A} : shf A -> forall {Δ} {ρ : Δ ≤ Γ}, shf (PSh_PSh ρ A).
  Proof.
    intros hAshf ?? Ξ wfΞ ρΞ i new hAt hAf.
    unfold PSh_PSh, shf in *.
    eapply hAshf.
    - refine (PSh_rew A _ _ _ _ hAt); constructor; reflexivity.
    - refine (PSh_rew A _ _ _ _ hAf); constructor; reflexivity.
  Qed.


  Lemma Split_shf {Γ} {A : PSh Γ} : shf (fun Δ wfΔ ρ => Split (fun Ξ wfΞ ρΞ => A Ξ wfΞ (ρΞ ∘w ρ))).
  Proof.
    intros Δ wfΔ ρ i new [wft dAt hAt] [wff dAf hAf].
    refine (Build_Split wfΔ (node Δ i new dAt dAf) _).
    intros Ξ wfΞ ρΞ oA. unfold overtree in oA. cbn in oA.
    destruct (decide_in (list_at Ξ (ren_index ρΞ i)) new) as [[] hin|hnotin].
    - specialize (hAt Ξ wfΞ (wk_new i new true ρΞ hin)).
      refine (PSh_rew A _ _ _ _ _).
      2: eapply hAt, oA.
      constructor; reflexivity.
    - specialize (hAf Ξ wfΞ (wk_new i new false ρΞ hin)).
      refine (PSh_rew A _ _ _ _ _).
      2: eapply hAf, oA.
      constructor; reflexivity.
    - destruct oA.
  Qed.



Definition over {Γ : context} (d : DTree Γ) (A: PSh Γ) :=
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree d ρ -> A Δ wfΔ ρ.


Lemma over_PSh {Γ: context} {d : DTree Γ} {A: PSh Γ} : over d A ->
  forall Δ (ρ : Δ ≤ Γ) (d' : DTree Δ),
    (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree d' ρΞ -> overtree d (ρΞ ∘w ρ)) ->
    over d' (PSh_PSh ρ A).
Proof.
  intros od ??? hdd' Ξ wfΞ ρΞ od'.
  now apply od.
Qed.

Lemma over_new : forall {Γ} (A : PSh Γ) {i new} (b:bool) {dt df}, over (node _ i new dt df) A ->
  over (Γ:=Γ,, i : new ↦ b) (if b return _ then dt else df) (PSh_PSh (wk_Fstep i new b wk_id) A).
Proof.
  intros * hA.
  eapply over_PSh; [apply hA|].
  intros Δ wfΔ ρ hover.
  eapply over_DTree_PSh_inv.
  unfold overtree in *.
  cbn [DTree_PSh].
  unshelve erewrite (decide_in_in _  new b _).
  1: eapply in_wk_Fstep.
  rewrite DTree_PSh_compose.
  eapply (eq_sind (overtree0 Δ) hover).
  eapply DTree_PSh_eq, eq_refl.
  cbn; now rewrite _wk_comp_runit.
Qed.
(* 
Lemma overtree_nil {L ρε} (wρε  : well_Fweakening ρε L nil) (d : DTree nil) : overtree d wρε.
Proof.
  remember nil as L'.
  induction wρε.
  + constructor.
  + eapply IHwρε, HeqL'.
  + inversion HeqL'.
Qed. *)

Lemma Split_bind_alg@{i j} : forall {Γ} {A : PSh@{i} Γ} {B: PSh@{j} Γ},
  shf@{j} B -> forall (hA : Split@{i} A),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA ρ -> B Δ wfΔ ρ)->
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
  intros [Γ L] * hBshf [wfΓ dA hA] hB; cbn in *.
  induction dA as [L |L i new dt ihAt df ihAf].
  - intros Δ wfΔ ρ; cbn in *.
    eapply hB. constructor.
  - change L with (Fctx (Build_context Γ L)) in new, i.
    specialize (ihAt (PSh_PSh (wk_Fstep i new true wk_id) A)
      (PSh_PSh (wk_Fstep i new true wk_id) B)
      (shf_PSh hBshf) (wfc_consF wfΓ)
      (over_new A true hA) (over_new B true hB)).
    specialize (ihAf (PSh_PSh (wk_Fstep i new false wk_id) A)
      (PSh_PSh (wk_Fstep i new false wk_id) B)
      (shf_PSh hBshf) (wfc_consF wfΓ)
      (over_new A false hA) (over_new B false hB)).
    intros Δ wfΔ ρ.
    destruct (decide_in (list_at Δ (ren_index ρ i)) new) as [[] hin|hnotin].
    + specialize (ihAt Δ wfΔ (wk_new i new true ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAt).
      rewrite <- wk_comp_runit.
      constructor; reflexivity.
    + specialize (ihAf Δ wfΔ (wk_new i new false ρ hin)).
      refine (PSh_rew B _ _ ρ _ ihAf).
      rewrite <- wk_comp_runit.
      constructor; reflexivity.
    + set (new' := Build_newnat _ new hnotin).
      eapply hBshf; tea.
      * specialize (ihAt (Δ,, (ren_index ρ i) : new' ↦ true)
          (wfc_consF wfΔ) (wk_Fup true ρ i new new' eq_refl)).
        refine (PSh_rew B _ _ _ _ ihAt).
        rewrite <- wk_comp_runit.
        constructor; reflexivity.
      * specialize (ihAf (Δ,, (ren_index ρ i) : new' ↦ false)
          (wfc_consF wfΔ) (wk_Fup false ρ i new new' eq_refl)).
        refine (PSh_rew B _ _ _ _ ihAf).
        rewrite <- wk_comp_runit.
        constructor; reflexivity.
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
  unfold overtree in *.
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
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA.(dtree) ρ ->
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
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA.(dtree) ρ ->  B Δ wfΔ ρ) ->
  Split B.
Proof.
  intros ???? hB.
  assert (wfΓ : [|-Γ]) by apply hA.
  now exists hA.
Qed.

Lemma Split_wk_bind : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) {B : PSh Δ},
    (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA.(dtree) (ρΞ ∘w ρ) ->
      Split (fun Θ wfΘ (ρΘ : Θ ≤ Ξ) => B Θ wfΘ (ρΘ∘w ρΞ))) ->
    Split B.
Proof.
  intros ??????? hB.
  set (hA' := Split_wkn hA wfΔ ρ).
  unshelve eapply Split_bind.
  2: apply hA'.
  intros Ξ wfΞ ρΞ ohA'.
  apply hB; tea.
  now eapply over_DTree_PSh_inv.
Qed.

Lemma Split_wk_bind_return : forall {Γ} {A : PSh Γ} (hA : Split A),
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) {B : PSh Δ},
  (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA.(dtree) (ρΞ ∘w ρ) -> B Ξ wfΞ ρΞ) ->
  Split B.
Proof.
  intros ??????? hB.
  refine (Build_Split wfΔ (DTree_PSh ρ hA) _).
  intros Ξ wfΞ ρΞ ohA.
  eapply hB; tea.
  now eapply over_DTree_PSh_inv.
Qed.


Definition dover {Γ} {A : PSh Γ} (hA : Split A) (P : dPSh Γ A)
  := forall Δ wfΔ (ρ : Δ ≤ Γ) (ohA : overtree hA ρ),
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
    forall (ohA : overtree hA ρ), P Δ wfΔ ρ (hA.(cover) Δ wfΔ ρ ohA)).


Lemma dSplit_bind_alg : forall {Γ} {A B: PSh Γ} {P},
  shf B -> forall {hA : Split A} (hP : dSplit P hA),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA ρ -> overtree hP ρ -> B Δ wfΔ ρ)->
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
  now eapply over_DTree_PSh_inv.
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
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA ρ -> overtree hP ρ ->
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
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA ρ -> overtree hP ρ -> B Δ wfΔ ρ) ->
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
  refine (Build_Split wfΔ (DTree_PSh ρ hP.(dtree)) _).
  intros Ξ wfΞ ρΞ ohP ohA.
  eapply hP; tea.
  now eapply over_DTree_PSh_inv.
Defined.

Lemma dSplit_wk_bind {Γ} {A : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) (B : PSh Δ),
    (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA (ρΞ ∘w ρ) ->
      overtree hP (ρΞ ∘w ρ) -> Split (fun Θ wfΘ (ρΘ : Θ ≤ Ξ) => B Θ wfΘ (ρΘ ∘w ρΞ))) ->
    Split B.
Proof.
  intros ???? hB.
  eapply (dSplit_bind (dSplit_wkn hP wfΔ ρ)).
  intros Ξ wfΞ ρΞ ohA ohP.
  eapply hB; tea.
  all: now eapply over_DTree_PSh_inv.
Qed.

Lemma dSplit_wk_bind_return {Γ} {A : PSh Γ} {P : dPSh Γ A}
  {hA : Split A} (hP : dSplit P hA) :
  forall {Δ} (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ) (B : PSh Δ),
  (forall Ξ (wfΞ : [|-Ξ]) (ρΞ : Ξ ≤ Δ), overtree hA (ρΞ ∘w ρ) -> overtree hP (ρΞ ∘w ρ) -> B Ξ wfΞ ρΞ) ->
  Split B.
Proof.
  intros ???? hB.
  unshelve eapply (dSplit_wk_bind hP wfΔ ρ).
  intros ??? ohA ohP.
  eapply Split_return; tea.
  intros Θ wfΘ ρΘ.
  eapply hB; tea.
  all: rewrite wk_comp_assoc; now eapply overtree_PSh.
Qed.

End Sheaves.

Arguments Build_Split {_ _ _ _}.
Arguments wfc_Split {_ _ _ _}.
Arguments dtree {_ _ _ _}.
Arguments cover {_ _ _ _}.



From LogRel Require Import Utils Syntax.All GenericTyping.
From Equations Require Import Equations.

Inductive DTree0 : Set :=
  | leaf : DTree0 
  | node (n : nat):
    DTree0 ->
    DTree0 ->
    DTree0.
Derive NoConfusion EqDec for DTree0.



Fixpoint overtree0 (d : DTree0) L' : SProp :=
  match d with
  | leaf => STrue
  | @node n dt df =>
    match decide_in L' n with
    | is_in true _ => overtree0 dt L'
    | is_in false _ => overtree0 df L'
    | is_notin _ => SFalse
    end
  end.

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


(* Fixpoint DTree_PSh {L} L' {Fρ : L' ≤ε L} : DTree L -> DTree L'.
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
Defined. *)

(* Lemma over_DTree_PSh {L L' L'' : Fcontext} {Fρ : L' ≤ε L} (d : DTree L) :
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
Qed. *)


(* Lemma over_DTree_PSh_inv (L L' L'' : Fcontext) (Fρ : L' ≤ε L) (Fρ' : L'' ≤ε L') (d : DTree L) :
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
Qed. *)


Lemma overtree0_PSh {L L' : Fcontext} (Fρ : L' ≤ε L) {d} :
  overtree0 d L -> overtree0 d L'.
Proof.
  intros od.
  induction d as [ | n dt ihdt df ihdf].
  + constructor.
  + cbn in *.
    destruct (decide_in L n) as [[] hin| hnotin].
    - rewrite (decide_in_in L' n _ (Fρ _ _ hin)); auto.
    - rewrite (decide_in_in L' n _ (Fρ _ _ hin)); auto.
    - destruct od.
Qed.
(* Lemma overtree0_PSh {L L' L'' : Fcontext} {Fρ : L'' ≤ε L'} (d : DTree L) :
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
Qed. *)


Fixpoint DTree (L : list Fcontext) : Set := match L with
  nil => unit
  | cons F L => prod DTree0 (DTree L) end.

(* Inductive well_DTree : list Fcontext -> DTree -> Set :=
  | well_nil : well_DTree nil nil
  | well_cons d0 d F L : well_DTree L d -> well_DTree (cons F L) (cons d0 d).
Derive Signature for well_DTree.


Lemma well_cons_inv {F L d} (P : forall F L d, well_DTree (cons F L) d -> Type) :
  (forall d0 d' wd', P F L (cons d0 d') (well_cons d0 d' F L wd')) ->
  forall (wd : well_DTree (cons F L) d), P F L d wd.
Proof.
  intros H wd. revert H. pattern F, L, wd.
  change (?A F L wd) with (match cons F L return forall wd, Type with
    cons F L => A F L
    | nil => fun _ => unit end wd).
  destruct wd; auto.
  constructor.
Defined.

Lemma Swell_cons_inv {F L d} (P : forall F L d, well_DTree (cons F L) d -> SProp) :
  (forall d0 d' wd', P F L (cons d0 d') (well_cons d0 d' F L wd')) ->
  forall (wd : well_DTree (cons F L) d), P F L d wd.
Proof.
  intros H wd. revert H. pattern F, L, wd.
  change (?A F L wd) with (match cons F L return forall wd, SProp with
    cons F L => A F L
    | nil => fun _ => STrue end wd).
  destruct wd; auto.
  constructor.
Defined.

Lemma well_nil_inv {d} (P : forall d, well_DTree nil d -> Type) :
  P nil well_nil ->
  forall (wd : well_DTree nil d), P d wd.
Proof.
  intros H wd. revert H. pattern wd.
  change (?A wd) with (match @nil Fcontext return forall wd, Type with nil => A | cons _ _ => fun _ => unit end wd).
  destruct wd; auto.
  constructor.
Defined.

Lemma Swell_nil_inv (P : forall d, well_DTree nil d -> SProp) :
  P nil well_nil ->
  forall {d} (wd : well_DTree nil d), P d wd.
Proof.
  intros H d wd. revert H. pattern wd.
  change (?A wd) with (match @nil Fcontext return forall wd, SProp with nil => A | cons _ _ => fun _ => STrue end wd).
  destruct wd; auto.
  constructor.
Defined. *)


Fixpoint overtree {L L' ρε} (d : DTree L) (wρε  : well_Fweakening ρε L' L) {struct wρε} : SProp :=
  match wρε with
  | well_emptyF => fun _ => STrue
  | well_stepF _ _  wρε => fun d => overtree d wρε
  | well_upF F F' _ wρε _ => fun '(pair d0 d) => SAnd (overtree0 d0 F) (overtree d wρε)
  end d.

Fixpoint DTree0_fusion d d' {struct d} := match d with
  | leaf => d'
  | node n dt df => node n (DTree0_fusion dt d') (DTree0_fusion df d')
  end.
Fixpoint DTree_fusion {L} : DTree L -> DTree L -> DTree L :=
  match L as l return DTree l -> DTree l -> DTree l with
  | nil => fun _ _ => tt
  | cons F L => fun '(dl0, dl') '(dr0, dr') => (DTree0_fusion dl0 dr0, DTree_fusion dl' dr')
  end.
Definition DTree_node L i new : DTree (Fcons L i new true) -> DTree (Fcons L i new false) ->
  DTree L.
Proof.
  intros dt df.
  induction i; cbn in *.
  + destruct dt as [dt0 dt'], df as [df0 df'].
    exact (pair (node new dt0 df0) (DTree_fusion dt' df')).
  + destruct dt as [dt0 dt'], df as [df0 df'].
    exact (pair (DTree0_fusion dt0 df0) (IHi new dt' df')).
Defined.
Lemma overtree0_fusion_inv {L dl dr} :
  overtree0 (DTree0_fusion dl dr) L -> SAnd (overtree0 dl L) (overtree0 dr L).
Proof.
  intros ofusion.
  induction dl as [| n dll IHdll dlr IHdlr]; cbn in *.
  - repeat constructor. exact ofusion.
  - destruct (decide_in L n) as [[] hin| hnotin].
    + specialize (IHdll ofusion) as []; repeat constructor; auto.
    + specialize (IHdlr ofusion) as []; repeat constructor; auto.
    + destruct ofusion.
Qed.
Lemma overtree_fusion_inv {L L' ρε} (wρε : well_Fweakening ρε L' L) dl dr :
  overtree (DTree_fusion dl dr) wρε -> SAnd (overtree dl wρε) (overtree dr wρε).
Proof.
  intros ofusion.
  induction wρε.
  + repeat constructor.
  + eapply IHwρε, ofusion.
  + destruct dl as [dl0 dl'], dr as [dr0 dr'].
    destruct ofusion as [h0 ofusion'].
    repeat constructor.
    - now eapply overtree0_fusion_inv in h0.
    - now eapply IHwρε in ofusion'.
    - now eapply overtree0_fusion_inv in h0.
    - now eapply IHwρε in ofusion'.
Qed.

Lemma overtree_node_inv {L L' ρε} (wρε : well_Fweakening ρε L' L) {i} {new : newnat (list_at L i)} b {dt df}
  (hin : in_Fctx (list_at L' (ren_index wρε i)) new b) :
  overtree (DTree_node L i new dt df) wρε ->
  overtree (if b return (DTree (Fcons L i new b)) then dt else df) (εwk_new i new b wρε hin).
Proof.
  intros onode.
  induction wρε.
  - inversion i.
  - eapply IHwρε, onode.
  - revert f wρε hin onode IHwρε.
    induction i using index_caseS; intros.
    * destruct dt as [dt0 dt'], df as [df0 df'], onode as [hF [odt' odf']%overtree_fusion_inv].
      cbn in hF, hin.
      rewrite (decide_in_in _ _ _ hin) in hF.
      replace (εwk_new (index_0 F' L') new b (well_upF F F' ρ wρε f) hin)
        with (well_upF F (Fcons' F' new b) ρ wρε (Fwk_new new b f hin))
        by eapply well_Fwk_irr.
      destruct b; constructor; tea.
    * destruct dt as [dt0 dt'], df as [df0 df'], onode as [[odt0 odf0]%overtree0_fusion_inv ofusion].
      cbn in hin.
      replace (εwk_new (index_S F' L' i) new b (well_upF F F' ρ wρε f) hin)
        with (well_upF _ _ _ (εwk_new i new b wρε hin) f)
        by eapply well_Fwk_irr.
      destruct b; constructor; eauto.
Qed.

Lemma overtree0_node_in F n dl dr : overtree0 (node n dl dr) F -> not_in_Fctx F n -> SFalse.
Proof.
  intros h0 hnotin.
  cbn in h0.
  destruct (decide_in F n) as [[] hin| hnotin']; tea.
  all : now eapply notin_is_not_in.
Qed.
Lemma overtree_node_in {L L' ρε} (wρε : well_Fweakening ρε L' L) {i} {new : newnat (list_at L i)} {dt df} :
  overtree (DTree_node L i new dt df) wρε -> not_in_Fctx (list_at L' (ren_index wρε i)) new -> SFalse.
Proof.
  intros onode.
  induction wρε.
  + inversion i.
  + eapply IHwρε, onode.
  + revert f wρε onode IHwρε.
    induction i using index_caseS; intros.
    - destruct dt as [dt0 dt'], df as [df0 df'], onode as [h0 onode'].
      now eapply overtree0_node_in.
    - destruct dt as [dt0 dt'], df as [df0 df'], onode as [h0 onode']; eauto.
Qed.

Fixpoint DTree_PSh {L L' ρε} (wρε  : well_Fweakening ρε L' L) (d : DTree L) : DTree L':=
  match wρε in well_Fweakening _ L' L return DTree L -> DTree L' with
  | well_emptyF => fun _ => tt
  | well_stepF _ _ wρε => fun d => pair leaf (DTree_PSh wρε d)
  | well_upF _ _ _ wρε _ =>fun '(pair d0 d') => pair d0 (DTree_PSh wρε d')
  end d.


Lemma over_DTree_PSh {L L' L'' ρε ρε'}
  (wρε  : well_Fweakening ρε L' L) (wρε'  : well_Fweakening ρε' L'' L')
  (d : DTree L) :
  overtree d (well_Fwk_compose wρε' wρε) ->
  overtree (DTree_PSh wρε d) wρε'.
Proof.
  intros od.
  induction wρε' in L, ρε, wρε, d, od |-*.
  - constructor.
  - eapply IHwρε', od.
  - inversion wρε; subst.
    + destruct (well_Fwk_irr (well_stepF F' ρ0 H3) wρε).
      rename H3 into wρε.
      cbn. repeat constructor.
      eapply IHwρε', od.
    + destruct (well_Fwk_irr (well_upF F' F'0 ρ0 H2 H4) wρε).
      rename H2 into wρε, H4 into f0.
      destruct d as [d0 d'], od as [hd0 od'].
      constructor; auto.
Qed.

Lemma over_DTree_PSh_inv {L L' L'' ρε ρε'}
  (wρε  : well_Fweakening ρε L' L) (wρε' : well_Fweakening ρε' L'' L')
  (d : DTree L) :
  overtree (DTree_PSh wρε d) wρε' ->
  overtree d (well_Fwk_compose wρε' wρε).
Proof.
  intros od.
  induction wρε' in L, ρε, wρε, d, od |-*.
  - inversion wρε; subst.
    destruct (well_Fwk_irr well_emptyF wρε).
    cbn in *.
    constructor.
  - eapply IHwρε', od.
  - inversion wρε; subst.
    * destruct (well_Fwk_irr (well_stepF F' ρ0 H3) wρε).
      rename H3 into wρε.
      eapply IHwρε', od.
    * destruct (well_Fwk_irr (well_upF F' F'0 ρ0 H2 H4) wρε).
      rename H2 into wρε, H4 into f0.
      destruct d as [d0 d'], od as [hd0 od'].
      constructor; auto.
Qed.

Definition DTree0_le d d' := forall F, overtree0 d' F -> overtree0 d F.
Fixpoint DTree_le {L} (d1 d2 : DTree L) : SProp :=
  match L return DTree L -> DTree L -> SProp with
  | nil => fun _ _ => STrue
  | cons F L =>  fun '(d10, d1') '(d20, d2') =>
    SAnd (DTree0_le d10 d20) (DTree_le d1' d2')
  end d1 d2.

Lemma DTree_le_trans {L} (d1 d2: DTree L) : DTree_le d2 d1 ->
  forall d3, DTree_le d3 d2 -> DTree_le d3 d1.
Proof.
  intros hle12 d3 hle23.
  induction L.
  + constructor.
  + destruct d1 as [d10 d1'], d2 as [d20 d2'], d3 as [d30 d3'],
      hle12 as [hle120 hle12'], hle23 as [hle230 hle23'].
    constructor.
    - intros F hover.
      auto.
    - now eapply IHL.
Qed.
Lemma DTree_le_refl {L} (d : DTree L) : DTree_le d d.
Proof.
  induction L.
  + constructor.
  + destruct d as [d0 d'].
    constructor.
    - intros F; auto.
    - auto.
Qed.

Definition DTree_lt {L} (d1 d2 : DTree L) :=
  SAnd (DTree_le d1 d2) (DTree_le d2 d1 -> SFalse).

Inductive Acc_DTree {L} (d : DTree L) :=
  | Acc_dtree_intro : (forall d', DTree_lt d' d -> Acc_DTree d') -> Acc_DTree d.
Lemma not_node_le n d1 d2 : DTree0_le (node n d1 d2) leaf -> SFalse.
Proof.
  intros hle.
  specialize (hle Fnil SI). cbn in hle.
  set (new := (Build_newnat Fnil n (not_in_nil n))).
  change (decide_in nil n) with (decide_in Fnil new) in hle.
  now rewrite decide_in_new in hle.
Qed.

Lemma Acc_le {L} (d d': DTree L): DTree_le d d' -> Acc_DTree d' -> Acc_DTree d.
Proof.
  intros hle hacc.
  induction hacc as [d' hacc IHhacc] in d, hle |- *.
  constructor.
  intros d'' hlt.
  eapply IHhacc.
  - constructor.
    + now eapply DTree_le_trans, hlt.
    + intros hle'.
      now eapply hlt, DTree_le_trans, hle.
  - eapply DTree_le_refl.
Qed.

(* Record DTree_le_node_concl (n : nat) (ds0 d0l d0r : DTree0) := {
  ds0l : DTree0;
  d0l_le : DTree0_le ds0l d0l;
  ds0r : DTree0;
  d0r_le : DTree0_le ds0r d0r;
  dnode_le : DTree0_le (node n ds0l ds0r) ds0;
  }.

Lemma DTree_le_node (n : nat) (ds0 d0l d0r : DTree0) : DTree0_le ds0 (node n d0l d0r) ->
  DTree_le_node_concl n ds0 d0l d0r.
Proof.
  intros hle.
  refine {| ds0l := DTree0_fusion d0l ds0; ds0r := DTree0_fusion d0r ds0|}.
  + intros F hF.
    eapply DTree0_fusion_inv.
    eapply hle.
    cbn. *)

Lemma all_Acc {L} (d: DTree L) : Acc_DTree d.
Proof.
  induction L.
  - constructor.
    intros d' nled'%Spr2.
    destruct (nled' SI).
  - destruct d as [d0 d'].
    specialize (IHL d').
    induction IHL as [d' Hacclt IHacclt].
    destruct d0 as [|n d0l d0r].
    + constructor.
      intros [ds0 ds'] hlt.
      destruct ds0.
      * eapply IHacclt.
        destruct hlt as [[_ hlt] hlne].
        constructor. easy.
        intros. eapply hlne.
        constructor. constructor.
        eapply H.
      * assert (err :SFalse); [|destruct err].
        destruct hlt as [[hle _] _].
        eapply not_node_le, hle.
    + constructor.
      intros [ds0 ds'] hlt.
      admit.
Admitted.

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
    now eapply over_DTree_PSh_inv.
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
    refine (Build_Split wfΔ (DTree_node Δ i new dAt dAf) _).
    intros Ξ wfΞ ρΞ oA.
    destruct (decide_in (list_at Ξ (ren_index ρΞ i)) new) as [[] hin|hnotin].
    - specialize (hAt Ξ wfΞ (wk_new i new true ρΞ hin)).
      refine (PSh_rew A _ _ _ _ _).
      2: eapply hAt, (overtree_node_inv ρΞ true), oA.
      constructor; reflexivity.
    - specialize (hAf Ξ wfΞ (wk_new i new false ρΞ hin)).
      refine (PSh_rew A _ _ _ _ _).
      2: eapply hAf, (overtree_node_inv ρΞ false), oA.
      constructor; reflexivity.
    - destruct (overtree_node_in _ oA hnotin).
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

(* Lemma over_new : forall {Γ} (A : PSh Γ) {i new} (b:bool) {dt df}, over (DTree_node _ i new dt df) A ->
  over (Γ:=Γ,, i : new ↦ b) (if b return _ then dt else df) (PSh_PSh (wk_Fstep i new b wk_id) A).
Proof.
  intros * hA.
  eapply over_PSh; [apply hA|].
  intros Δ wfΔ ρ hover.
  eapply over_DTree_PSh_inv.
  cbn.
  rewrite (decide_in_in _  new b (Fwk ρ new b (in_hereF _ new b))).
  now destruct b.
Qed. *)

Lemma overtree_nil {L ρε} (wρε  : well_Fweakening ρε L nil) (d : DTree nil) : overtree d wρε.
Proof.
  remember nil as L'.
  induction wρε.
  + constructor.
  + eapply IHwρε, HeqL'.
  + inversion HeqL'.
Qed.

Lemma Split_bind_alg@{i j} : forall {Γ} {A : PSh@{i} Γ} {B: PSh@{j} Γ},
  shf@{j} B -> forall (hA : Split@{i} A),
  (forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), overtree hA ρ -> B Δ wfΔ ρ)->
  forall Δ (wfΔ : [|-Δ]) (ρ : Δ ≤ Γ), B Δ wfΔ ρ.
Proof.
(*   intros [Γ L] * hBshf [wfΓ dA hA] hB. *)
  intros [Γ L] ?? hBshf [wfΓ dA hA] hB Δ wfΔ ρ; cbn in *.
  pose proof (all_Acc dA) as accA.
  induction accA.
  eapply X.
  induction L in Γ,Δ,A,B, wfΔ, wρε, ρ, wρ, dA, hA, hB |-*.
  - eapply hB, overtree_nil.
  - destruct dA as [dA0 dA'].
    induction dA0. cbn in hA.
    +  eapply IHL.
    set (ρ' := Build_wk_well_wk _ ((Build_context Γ L) ,, ↦ a) ρε wρε ρ wρ).
    eapply IHL.
    eapply hBshf.
    eapply hB. specialize (IHwρε A B hBshf wfΓ dA hA hB).

(*   induction L. *)
(*   intros Γ ?? hBshf [wfΓ dA hA] hB Δ wfΔ ρ; cbn in *.
  revert A B hBshf wfΓ dA hA hB wfΔ.
  induction ρ using wk_induction; clear Γ Δ; try rename Γ0 into Γ, Δ0 into Δ; intros.
  + intros.
    eapply hB.
    constructor.
  + generalize dependent Δ. eapply IHρ. specialize (IHρ A0 B hBshf wfΓ dA hA hB).
  + admit.
  + 
  specialize (IHρ A (fun Δ wfΔ
   cbn in dA.
  induction wρε in L, wρε, Δ, wfΔ, ρ, wρ, A, B, hBshf, dA, hA, hB|-*.
  + eapply hB.
    constructor.
  + inversion wρ; subst.
    admit.
  + destruct dA. cbn in *. *)



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



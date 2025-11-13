(** * LogRel.LogicalRelation.Induction: good induction principles for the logical relation. *)
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation Monad.

Set Universe Polymorphism.

(** As Coq is not currently able to define induction principles for nested inductive types
as our LR, we need to prove them by hand. We use this occasion to write down principles which
do not directly correspond to what LR would give us. More precisely, our induction principles:
- handle the two levels uniformly, rather than having to do two separate
  proofs, one at level zero and one at level one;
- apply directly to an inhabitant of the bundled logical relation, rather than the raw LR;
- give a more streamlined minor premise to prove for the case of Π type reducibility,
  which hides the separation needed in LR between the reducibility data and its adequacy
  (ie the two ΠA and ΠAad arguments to constructor LRPi).
Also, and crucially, all induction principles are universe-polymorphic, so that their usage
does not create global constraints on universes. *)

Section Inductions.
  Context `{ta : tag}
    `{!WfContext ta} `{!WfType ta} `{!Typing ta}
    `{!ConvType ta} `{!ConvTerm ta} `{!ConvNeuConv ta}
    `{!RedType ta} `{!RedTerm ta}.

(** ** Embedding *)

(** Reducibility at a lower level implies reducibility at a higher level, and their decoding are the
same. Both need to be proven simultaneously, because of contravariance in the product case. *)
  Fixpoint LR_embedding@{i j k l} {l l'} (l_ : l << l')
    {Γ A B tmeq} (lr : LogRel@{i j k l} l Γ A B tmeq) {struct lr}
    : (LogRel@{i j k l} l' Γ A B tmeq) :=
    let embedPolyAd {Γ A A' B B'} {PA : PolyRedPack Γ A A' B B'} (PAad : PolyRedPackAdequate _ PA) :=
        {|
          PolyRedPack.shpAd (Δ : context) (ρ : Δ ≤ _) (h : [  |- Δ]) :=
            LR_embedding l_ (PAad.(PolyRedPack.shpAd) ρ h) ;
          PolyRedPack.posAd (Δ : context) (a b : term) (ρ : Δ ≤ _) (h : [  |- Δ])
              (ha : [PolyRedPack.shpRed PA ρ h | Δ ||- a ≅ b : _]) :=
            dover_apply (fun _ _ _ => LR_embedding l_) (PAad.(PolyRedPack.posAd) ρ h ha)
        |}
    in
    match lr with
    | LRU _ hΓ H =>
        match
          (match l_ with Oi => fun H' => elim (H' _ wk_id hΓ).(URedTy.lt) end H)
        with end
    | LRne _ hΓ neA => LRne _ hΓ neA
    | LRPi _ ΠA ΠAad => LRPi _ ΠA (embedPolyAd ΠAad)
    | LRNat _ NA => LRNat _ NA
    | LRBool _ NA => LRBool _ NA
    | LREmpty _ NA => LREmpty _ NA
    | LRSig _ PA PAad => LRSig _ PA (embedPolyAd PAad)
    | LRId _ hΓ IA IAad => LRId _ hΓ IA (fun Δ ρ hΔ => {| IdRedTyPack.tyAd := LR_embedding l_ (IAad _ _ _).(IdRedTyPack.tyAd) ; |})
    end.


  (** A basic induction principle, that handles only the first point in the list above *)

  Notation PolyHyp P Γ ΠA HAad G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (HAad.(PolyRedPack.shpAd) ρ h)) ->
      (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
        (ha : [ ΠA.(PolyRedPack.shpRed) ρ h | Δ ||- a ≅ b: _ ]),
        ddover (fun _ _ _ => P) (HAad.(PolyRedPack.posAd) ρ h ha)) -> G).

  Theorem LR_rect@{i j k o}
    (l : TypeLevel)
    (rec : forall l', l' << l -> RedRel@{i j})
    (P : forall {Γ A B tmeq}, LR@{i j k} rec Γ A B tmeq  -> Type@{o}) :

    (forall (Γ : context) A B (hΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRU rec hΓ h)) ->

    (forall (Γ : context) (A B : term) hΓ (neA : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> [Δ ||-Sne A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRne rec hΓ neA)) ->

    (forall (Γ : context) (A B : term) (ΠA : PiRedTyPack@{j k} Γ A B) (HAad : PiRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRPi rec ΠA HAad))) ->

    (forall Γ A B (NA : [Γ ||-SNat A ≅ B]), P (LRNat rec NA)) ->

    (forall Γ A B (NA : [Γ ||-SBool A ≅ B]), P (LRBool rec NA)) ->

    (forall Γ A B (NA : [Γ ||-SEmpty A ≅ B]), P (LREmpty rec NA)) ->

    (forall (Γ : context) (A B : term) (ΠA : SigRedTyPack@{j k} Γ A B) (HAad : SigRedTyAdequate (LR rec) ΠA),
      PolyHyp P Γ ΠA HAad (P (LRSig rec ΠA HAad))) ->

    (forall Γ A B hΓ (IA : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> IdRedTyPack@{j} Δ A⟨ρ⟩ B⟨ρ⟩) (IAad : forall Δ (ρ : Δ ≤ Γ) (hΔ : [|-Δ]), IdRedTyAdequate (LR rec) (IA Δ ρ hΔ)),
      (forall Δ (ρ : Δ ≤ Γ) (hΔ : [|-Δ]), P (IAad Δ ρ hΔ).(IdRedTyPack.tyAd)) ->
      (* (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IAad.(IdRedTyPack.tyKripkeAd) ρ wfΔ)) -> *)
      P (LRId rec hΓ IA IAad)) ->

    forall (Γ : context) (A B : term) (tmeq  : term -> term -> Type@{j}) (lr : LR@{i j k} rec Γ A B tmeq),
      P lr.
  Proof.
    cbn.
    intros HU Hne HPi HNat HBool HEmpty HSig HId.
    fix HRec 5.
    destruct lr.
    - eapply HU.
    - eapply Hne.
    - eapply HPi.
      all: repeat intro; eapply HRec.
    - eapply HNat.
    - eapply HBool.
    - eapply HEmpty.
    - eapply HSig.
      all: repeat intro; eapply HRec.
    - eapply HId; intros; eapply HRec.
  Defined.

  Definition LR_rec@{i j k} := LR_rect@{i j k Set}.

  Notation PolyHypLogRel P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PolyRed.shpRed) ρ h).(LRAd.adequate)) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ Δ ||-< _ > a ≅ b : _ |  ΠA.(PolyRed.shpRed) ρ h ]),
      dover (fun _ _ hSplit => P (LRAd.adequate hSplit)) (ΠA.(PolyRed.posRed) ρ h ha)) -> G).



  (** Induction principle specialized to LogRel as the reducibility relation on lower levels *)
  Theorem LR_rect_LogRelRec@{i j k l o}
    (P : forall {l Γ A B tmeq}, LogRel@{i j k l} l Γ A B tmeq -> Type@{o}) :

    (forall l (Γ : context) A B hΓ (h : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRU (LogRelRec l) hΓ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) hΓ (neA : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> [Δ ||-Sne A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRne (LogRelRec l) hΓ neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      PolyHypLogRel P Γ ΠA (P (LRPi' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A B (NA : [Γ ||-SNat A ≅ B]), P (LRNat (LogRelRec l) NA)) ->

    (forall l Γ A B (NA : [Γ ||-SBool A ≅ B]), P (LRBool (LogRelRec l) NA)) ->

    (forall l Γ A B (NA : [Γ ||-SEmpty A ≅ B]), P (LREmpty (LogRelRec l) NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      PolyHypLogRel P Γ ΠA (P (LRSig' ΠA).(LRAd.adequate ))) ->

    (forall l Γ A B hΓ (IA : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SId<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      (forall Δ (ρ : Δ ≤ Γ) hΔ, P ((IA Δ ρ hΔ).(IdRedTy.tyRed).(LRAd.adequate))) ->
      (* (forall Δ (ρ : Δ ≤ Γ) (wfΔ : [|-Δ]), P (IA.(IdRedTy.tyKripke) ρ wfΔ).(LRAd.adequate)) -> *)

      P (LRId' hΓ IA).(LRAd.adequate)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (tmeq  : term -> term -> Type@{k})
      (lr : LR@{j k l} (LogRelRec@{i j k} l) Γ A B tmeq),
      P lr.
  Proof.
    intros ?? HPi ??? HSig HId **; eapply LR_rect@{j k l o}.
    1,2,4,5,6: auto.
    - intros; eapply (HPi _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HSig _ _ _ _ (ParamRedTy.from HAad)); eauto.
    - intros; eapply (HId _ _ _ _ _ (fun Δ ρ hΔ=> IdRedTy.from (IAad Δ ρ hΔ))) ; eauto.
  Defined.

  Notation PolyHypTyUr P Γ ΠA G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P (ΠA.(PolyRed.shpRed) ρ h)) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRed.shpRed) ρ h | Δ ||- a ≅ b : _ ]),
      dover (fun _ _ => P) (ΠA.(PolyRed.posRed) ρ h ha)) -> G).

  Theorem LR_rect_TyUr@{i j k l o}
    (P : forall {l Γ A B}, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> Type@{o}) :

    (forall l (Γ : context) A B hΓ (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRU_ hΓ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) hΓ (neA : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-Sne A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRne_ l hΓ neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      PolyHypTyUr P Γ ΠA (P (LRPi' ΠA))) ->

    (forall l Γ A B (NA : [Γ ||-SNat A ≅ B]), P (LRNat_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SBool A ≅ B]), P (LRBool_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SEmpty A ≅ B]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      PolyHypTyUr P Γ ΠA (P (LRSig' ΠA))) ->

    (forall l Γ A B hΓ (IA : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> [Δ ||-SId<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      (forall Δ (ρ : Δ ≤ Γ) hΔ, P (IA Δ ρ hΔ).(IdRedTy.tyRed)) ->
      P (LRId' hΓ IA)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (lr : [LogRel@{i j k l} l | Γ ||- A ≅ B]),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty HSig HId l Γ A B lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A B _ lr => P l Γ A B (LRbuild lr))).
    all: auto.
  Defined.

  Notation PolyHypRec P Γ ΠA A B G :=
    ((forall {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ]), P Δ A⟨ρ⟩ B⟨ρ⟩) ->
    (forall {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ])
      (ha : [ ΠA.(PolyRed.shpRed) ρ h | Δ ||- a ≅ b : _ ]),
      dover (fun _ _ => P) (ΠA.(PolyRed.posRed) ρ h ha)) -> G).

  Theorem LR_rec_TyUr@{i j k l o}
    (P : forall {l} Γ A B, Type@{o}) :

    (forall l (Γ : context) A B (h : [Γ ||-SU<l> A ≅ B]),
      P Γ A B) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) hΓ (neA : [Γ ||-Sne A ≅ B]),
      P Γ A B) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      PolyHypRec P Γ ΠA (P (LRPi' ΠA))) ->

    (forall l Γ A B (NA : [Γ ||-SNat A ≅ B]), P (LRNat_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SBool A ≅ B]), P (LRBool_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SEmpty A ≅ B]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      PolyHypTyUr P Γ ΠA (P (LRSig' ΠA))) ->

    (forall l Γ A B hΓ (IA : forall Δ (ρ : Δ ≤ Γ),[|-Δ] -> [Δ ||-SId<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      (forall Δ (ρ : Δ ≤ Γ) hΔ, P (IA Δ ρ hΔ).(IdRedTy.tyRed)) ->
      P (LRId' hΓ IA)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (lr : [LogRel@{i j k l} l | Γ ||- A ≅ B]),
      P lr.
  Proof.
    intros HU Hne HPi HNat HBool HEmpty HSig HId l Γ A B lr.
    apply (LR_rect_LogRelRec@{i j k l o} (fun l Γ A B _ lr => P l Γ A B (LRbuild lr))).
    all: auto.
  Defined.

  Theorem LR_case_TyUr@{i j k l o}
    (P : forall {l Γ A B}, [LogRel@{i j k l} l | Γ ||- A ≅ B] -> Type@{o}) :

    (forall l (Γ : context) A B hΓ (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRU_ hΓ h)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) hΓ (neA : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-Sne A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRne_ l hΓ neA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : PiRedTy@{i j k l} Γ l A B),
      P (LRPi' ΠA)) ->

    (forall l Γ A B (NA : [Γ ||-SNat A ≅ B]), P (LRNat_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SBool A ≅ B]), P (LRBool_ l NA)) ->

    (forall l Γ A B (NA : [Γ ||-SEmpty A ≅ B]), P (LREmpty_ l NA)) ->

    (forall (l : TypeLevel) (Γ : context) (A B : term) (ΠA : SigRedTy@{i j k l} Γ l A B),
      P (LRSig' ΠA)) ->

    (forall l Γ A B hΓ (IA : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SId<l> A⟨ρ⟩ ≅ B⟨ρ⟩]),
      P (LRId' hΓ IA)) ->

    forall (l : TypeLevel) (Γ : context) (A B : term) (lr : [LogRel@{i j k l} l | Γ ||- A ≅ B]),
      P lr.
  Proof. intros; now apply LR_rect_TyUr. Defined.

End Inductions.

(* induction lr using LR_rect_TyUr fails with "Cannot recognize the conclusion of an induction scheme" *)
(* the tactic indLR lr expects an identifier lr : [Γ ||-<l> A ≅ B]  and applies the induction principle *)
Ltac indLR lr :=
  match type of lr with
  | [ ?Γ ||-< ?l > ?A ≅ ?B ] =>
    pattern l, Γ, A, B, lr; apply LR_rect_TyUr; clear l Γ A B lr; intros l Γ A B
  end.

Ltac caseLR lr :=
  match type of lr with
  | [ ?Γ ||-< ?l > ?A ≅ ?B ] =>
    pattern l, Γ, A, B, lr; apply LR_case_TyUr; clear l Γ A B lr; intros l Γ A B
  end.

(** ** Inversion principles *)

Instance whredTyLR `{GenericTypingProperties} {Γ l} : WhRedTyRel Γ (LRAdequate Γ (LogRel l)).
Proof.
  unshelve econstructor; intros ?? lr; caseLR lr;
    try first [now eapply whredtyL | now eapply whredtyR | now eapply whredty_conv].
  + intros. specialize (h Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in h. eapply (whredtyL h).
  + intros. specialize (neA Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in neA. eapply (whredtyL neA).
  + intros. specialize (IA Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in IA. eapply (whredtyL IA).
  + intros. specialize (h Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in h. eapply (whredtyR h).
  + intros. specialize (neA Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in neA. eapply (whredtyR neA).
  + intros. specialize (IA Γ wk_id hΓ). do 2 rewrite wk_id_ren_on in IA. eapply (whredtyR IA).
  + intros; cbn. now apply convty_uni.
  + intros; cbn.
    set (neA' := neA Γ wk_id hΓ); clearbody neA'; clear neA; revert neA'.
    do 2 rewrite wk_id_ren_on; cbn.
    intros neA.
    eapply (whredty_conv (WhRedTyRel:=neRedTyWhRedTy)).
  + intros; cbn.
    set (IA' := IA Γ wk_id hΓ); clearbody IA'; clear IA; revert IA'.
    do 2 rewrite wk_id_ren_on; cbn.
    intros IA.
    eapply (whredty_conv (WhRedTyRel:=IdRedTyWhRed)).
Defined.

(* 
Instance whredTmLR `{GenericTypingProperties} {Γ A B l} (RAB : [Γ ||-<l> A ≅ B]) :
  WhRedTmRel Γ (whredtyL RAB).(tyred_whnf) (RAB.(LRPack.eqTm)).
Proof.
  caseLR RAB; intros; try typeclasses eauto.
  - cbn. apply URedTmEqWhRedRel.
  - apply neRedTmWhRedTm.
  - apply IdRedTmWhRedRel.
Defined. *)


Section Inversions.
  Context `{GenericTypingProperties}.

  Lemma whredL_conv {Γ l A B} (lr : [Γ ||-<l> A ≅ B]) : [Γ |- A ≅ (whredtyL lr).(tyred_whnf)].
  Proof.
    pose proof (whredty_conv lr); destruct (whredtyL lr); cbn in *.
    eapply convty_exp.
    1: gtyping.
    1: eapply redty_refl; gtyping.
    now eapply lrefl.
  Qed.

  Definition pidom (A : term) :=
    match A with | tProd dom _ => dom | _ => A end.


  Definition picod (A : term) :=
    match A with | tProd _ cod => cod | _ => A end.

  Definition sigdom (A : term) :=
    match A with | tSig dom _ => dom | _ => A end.

  Definition sigcod (A : term) :=
    match A with | tSig _ cod => cod | _ => A end.

  Definition idparam (A : term) :=
    match A with | tId P _ _ => P | _ => A end.

  Definition idlhs (A : term) :=
    match A with | tId _ lhs _ => lhs | _ => A end.

  Definition idrhs (A : term) :=
    match A with | tId _ _ rhs => rhs | _ => A end.

  Definition IdPShroot {Γ l A B} (hΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SId<l> A⟨ρ⟩ ≅ B⟨ρ⟩]) : [Γ ||-SId<l> A ≅ B].
  Proof.
    specialize (h Γ wk_id hΓ).
    now do 2 rewrite wk_id_ren_on in h.
  Defined.

  Definition NePShroot {Γ A B} (hΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-Sne A⟨ρ⟩ ≅ B⟨ρ⟩]) : [Γ ||-Sne A ≅ B].
  Proof.
    specialize (h Γ wk_id hΓ).
    now do 2 rewrite wk_id_ren_on in h.
  Defined.

  Definition UPShroot {Γ l A B} (hΓ : [|-Γ]) (h : forall Δ (ρ : Δ ≤ Γ), [|-Δ] -> [Δ ||-SU<l> A⟨ρ⟩ ≅ B⟨ρ⟩]) : [Γ ||-SU<l> A ≅ B].
  Proof.
    specialize (h Γ wk_id hΓ).
    now do 2 rewrite wk_id_ren_on in h.
  Defined.

  Definition invLRTyEqL {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (w : isType A') :=
    match w return Type with
    | UnivType => ∑ hΓ h, lr = LRU_ hΓ h
    | ProdType => ∑ (h : [Γ ||-Π<l> A ≅ B]), [× lr = LRPi' h, h.(ParamRedTy.domL) = pidom A' & h.(ParamRedTy.codL) = picod A']
    | NatType => ∑ (h : [Γ ||-SNat A ≅ B]), lr = LRNat_ l h
    | BoolType => ∑ (h : [Γ ||-SBool A ≅ B]), lr = LRBool_ l h
    | EmptyType => ∑ (h : [Γ ||-SEmpty A ≅ B]), lr = LREmpty_ l h
    | SigType => ∑ (h : [Γ ||-Σ<l> A ≅ B]), [× lr = LRSig' h, h.(ParamRedTy.domL) = sigdom A' & h.(ParamRedTy.codL) = sigcod A']
    | IdType => ∑ hΓ h, [× lr = LRId' hΓ h, (IdPShroot hΓ h).(IdRedTy.tyL) = idparam A', (IdPShroot hΓ h).(IdRedTy.lhsL) = idlhs A' & (IdPShroot hΓ h).(IdRedTy.rhsL) = idrhs A']
    | NeType _ => ∑ hΓ h, lr = LRne_ l hΓ h × (NePShroot hΓ h).(neRedTy.tyL) = A'
    end.

  Lemma invLREqL {Γ l A B A'} (lr : [Γ ||-<l> A ≅ B]) (r : [Γ | A ⤳* A']) (w : isType A') : invLRTyEqL lr w.
  Proof.
    assert (A' = (whredtyL lr).(tyred_whnf)); subst.
    1: eapply whred_det; try apply isType_whnf; tea; gtyping.
    rewrite (isType_uniq w (whredtyL lr).(tyred_whnf_isType)).
    clear r w;  indLR lr; cbn; intros ; repeat esplit.
  Qed.

  Lemma invLREqL_whred {Γ l l' A A' B} (RAA' : [Γ ||-<l'> A ≅ A']) (lr : [Γ ||-<l> A ≅ B]) : invLRTyEqL lr (whredtyL RAA').(tyred_whnf_isType).
  Proof. apply invLREqL; gtyping. Qed.

  Lemma invLREqL_whred' {Γ l l' A B C} (RAB : [Γ ||-<l> A ≅ B]) (lr : [Γ ||-<l'> B ≅ C]) : invLRTyEqL lr (whredtyR RAB).(tyred_whnf_isType).
  Proof. apply invLREqL; gtyping. Qed.

  Lemma invLRU {Γ l B} : [Γ ||-<l> U ≅ B] -> [Γ ||-SU<l> U ≅ B].
  Proof.
    intros hAB. epose proof (invLREqL hAB redIdAlg UnivType) as h. destruct h as (hΓ&h&_).
    apply (UPShroot hΓ h).
  Qed.

  Lemma invLRne {Γ l A B} : whne A -> [Γ ||-<l> A ≅ B] -> [Γ ||-Sne A ≅ B].
  Proof.
    intros hne hAB. epose proof (invLREqL hAB redIdAlg (NeType hne)) as h. destruct h as (hΓ&h&_).
    apply (NePShroot hΓ h).
  Qed.

  Lemma invLRΠ {Γ l dom cod B} : [Γ ||-<l> tProd dom cod ≅ B] -> [Γ ||-Π<l> tProd dom cod ≅ B].
  Proof.
    intros; now unshelve eapply  (invLREqL _ redIdAlg ProdType).π1.
  Qed.

  Lemma invLRΣ {Γ l dom cod B} : [Γ ||-<l> tSig dom cod ≅ B] -> [Γ ||-Σ<l> tSig dom cod ≅ B].
  Proof.
    intros; now unshelve eapply  (invLREqL _ redIdAlg SigType).π1.
  Qed.

  Lemma invLRId {Γ l A x y B} : [Γ ||-<l> tId A x y ≅ B] -> [Γ ||-SId<l> tId A x y ≅ B].
  Proof.
    intros hAB. epose proof (invLREqL hAB redIdAlg IdType) as h. destruct h as (hΓ&h&_).
    apply (IdPShroot hΓ h).
  Qed.

End Inversions.

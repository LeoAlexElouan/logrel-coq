(** * LogRel.LogicalRelation.Escape: the logical relation implies conversion/typing. *)
From Stdlib Require Import CRelationClasses.
From LogRel Require Import Utils Syntax.All LogicalRelation GenericTyping Monad.
From LogRel.LogicalRelation Require Import Induction.

Set Universe Polymorphism.

Section Escapes.
  Context `{GenericTypingProperties}.

  Lemma escapeTy {l Γ A B} (lr : [Γ ||-S< l > A ≅ B]) :
      [Γ |- A] × [Γ |- B] × [Γ |- A ≅ B].
  Proof.
    indLR lr.
    - intros []; prod_splitter; [ | | eapply convty_exp]; gen_typing.
    - intros []; prod_splitter; [ | | eapply convty_exp]; gen_typing.
    - intros [???? [] []] _ _; prod_splitter;[ | | eapply convty_exp]; gtyping.
    - intros []; prod_splitter; [| |eapply convty_exp]; gtyping.
    - intros []; prod_splitter; [| |eapply convty_exp]; gtyping.
    - intros []; prod_splitter; [| |eapply convty_exp]; gtyping.
    - intros []; prod_splitter; [| |eapply convty_exp]; gtyping.
    - intros [???? [] []] _ _; prod_splitter; [| |eapply convty_exp]; gtyping.
    - intros [] _ ; prod_splitter; [| |eapply convty_exp]; gtyping.
  Qed.

  Lemma escape {l Γ A B} :
      [Γ ||-S< l > A ≅ B] ->
      [Γ |- A].
  Proof.
    apply escapeTy.
  Qed.

  Lemma escapeEq {l Γ A B} (lr : [Γ ||-S< l > A ≅ B]) :
      [Γ |- A ≅ B].
  Proof.
    now eapply escapeTy.
  Qed.

  Lemma escapeSplitTy {l Γ A B} (lr : [Γ ||-<l> A ≅ B]) :
    [Γ |- A] × [Γ |- B] × [Γ |- A ≅ B].
  Proof.
    assert ([|-Γ]) by apply lr.
    prod_splitter.
    all: unshelve first [eapply (Split_bind_wft lr) | eapply (Split_bind_convty lr)]; tea; 
      intros;
      now first [eapply escape,lr| eapply escapeTy,lr].
  Qed.

  Lemma escapeSplit {l Γ A B} : [Γ ||-<l> A ≅ B] ->
    [Γ |- A].
  Proof.
    now unshelve eapply escapeSplitTy.
  Qed.

  Lemma escapeTm {l Γ A B t u} (lr : [Γ ||-S< l > A ≅ B]) :
    [Γ ||-S< l > t ≅ u : A | lr ] ->
    [Γ |- t : A] × [Γ |- u : A] × [Γ |- t ≅ u : A].
  Proof.
    generalize (whredL_conv lr); caseLR lr.
    - intros RU ? [[] []]; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct RU; eapply convtm_wfexp; gtyping.
    - intros neA ? []; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct neA; cbn in *; eapply convtm_wfexp.
      1-3: gtyping.
      2: now eapply urefl.
      eapply convtm_convneu; tea.
      econstructor; now eapply convneu_whne.
    - intros ΠA ? [[] []]; cbn in *; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct ΠA as [???? []]; cbn in *.
      eapply convtm_wfexp.
      1-3: gtyping.
      2: now eapply lrefl.
      tea.
    - intros NA ? []; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct NA; eapply convtm_wfexp.
      1-3: gen_typing.
      2: now eapply urefl.
      tea.
    - intros BA ? []; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct BA; eapply convtm_wfexp.
      1-3: gen_typing.
      2: now eapply urefl.
      tea.
    - intros EA ? [???? []]; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct EA; eapply convtm_wfexp.
      1-3: gen_typing.
      2: now eapply urefl.
      eapply convtm_convneu; tea; constructor.
    - intros TA ? Rtu; induction t, u, Rtu as [] using TreeRedTmEq.TreeRedTmEq_destruct; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct TA; eapply convtm_wfexp.
      1-3: gen_typing.
      2: now eapply urefl.
      tea.
    - intros ΣA ? [[] []]; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct ΣA as [???? []]; cbn in *; eapply convtm_wfexp.
      1-3: gtyping.
      2: now eapply urefl.
      tea.
    - intros IA ? []; cbn in *; prod_splitter.
      1,2: (eapply ty_conv; [gtyping|now symmetry]).
      destruct IA as []; cbn in *; eapply convtm_wfexp.
      1-3: gtyping.
      2: now eapply urefl.
      tea.
  Qed.

  Definition escapeTerm {l Γ t u A} (lr : [Γ ||-S< l > A ]) :
    [Γ ||-S< l > t ≅ u : A | lr ] ->
    [Γ |- t : A].
  Proof. apply escapeTm. Qed.

  Definition escapeEqTerm {l Γ t u A} (lr : [Γ ||-S< l > A ]) :
    [Γ ||-S< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof. apply escapeTm. Qed.

  Lemma escapeSplitTm {l Γ A B t u} (lr : [Γ ||-< l > A ≅ B]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t : A] × [Γ |- u : A] × [Γ |- t ≅ u : A].
  Proof.
    assert ([|-Γ]) by apply lr.
    intros htu.
    prod_splitter.
    all: unshelve first [eapply (dSplit_bind_ty htu) | eapply (dSplit_bind_convtm htu)]; tea;
      intros;
      now unshelve first [refine (fst (escapeTm _ _)); eapply htu|eapply escapeTm, htu].
  Qed.

  Definition escapeSplitTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t : A].
  Proof. apply escapeSplitTm. Qed.

  Definition escapeSplitEqTerm {l Γ t u A} (lr : [Γ ||-< l > A ]) :
    [Γ ||-< l > t ≅ u : A | lr ] ->
    [Γ |- t ≅ u : A].
  Proof. apply escapeSplitTm. Qed.

  Lemma escapeConv {l Γ A B} :
    [Γ ||-S<l> A ≅ B] ->
    [Γ |- B].
  Proof. apply escapeTy. Qed.



End Escapes.
(* 
Ltac escapeSplit :=
  repeat lazymatch goal with
  | [H : [_ ||-< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-<_> _ ≅ _  : _ | ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTm _ H) as (Xl & Xr & X) );
      block H
  end; unblock. *)

Ltac escape :=
  repeat lazymatch goal with
  | [H : [_ ||-S< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-S<_> _ ≅ _  : _ | ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeTm RA H) as (Xl & Xr & X) );
      block H
  | [H : [_ ||-< _ > _] |-  _ ] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTy H) as (Xl & Xr & X) );
    block H
  | [H : [_ ||-<_> _ ≅ _  : _ | ?RA ] |- _] =>
    try
     (let Xl := fresh "EscL" H in
      let Xr := fresh "EscR" H in
      let X := fresh "Esc" H in
      pose proof (escapeSplitTm _ H) as (Xl & Xr & X) );
      block H
  end; unblock.

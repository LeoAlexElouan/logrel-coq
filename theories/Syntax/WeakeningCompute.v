
From LogRel Require Import Utils AutoSubst.Extra Notations.
From LogRel.Syntax Require Import BasicAst Context NormalForms Computations Weakening.

Notation eta_expand' Γ A f := (tApp f⟨@wk1 Γ A⟩ (tRel 0)) (only parsing).
Notation arr' Γ A B := (tProd A (B⟨@wk1 Γ (A : term)⟩)).
Notation elimSuccHypTy' Γ P :=
  (tProd tNat (arr' (Γ,, tNat) P P⟨wk_up tNat (@wk1 Γ tNat)⟩[(tSucc (tRel 0))..])).
Notation elimLeafHypTy' Γ P :=
  (tProd tNat P⟨wk_up tTree (@wk1 Γ tNat)⟩[(tLeaf (tRel 0))..]).


Definition elimNodeHypTyCod (Γ : context) (P : term) := (arr' (Γ,, tNat,, tTree,,tTree) P[(tRel 1)..]
    (arr' (Γ,, tNat ,, tTree,,tTree) P[(tRel 0)..]
      (P[(tNode (tRel 2) (tRel 1) (tRel 0))..]))).
Definition elimNodeHypTy' Γ P :=
  (tProd tNat (tProd tTree (tProd tTree (elimNodeHypTyCod Γ P⟨wk_up tTree (@wk1 Γ tNat)⟩⟨wk_up tTree (@wk1 (Γ,,tNat) tTree)⟩⟨wk_up tTree (@wk1 (Γ,,tNat,,tTree) tTree)⟩)))).


Lemma wk_prod {A B : term} {Γ Δ} (ρ : Δ ≤ Γ) : tProd A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tProd A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now bsimpl. Qed.
Lemma wk_arr' {A B : term} {Γ Δ} (ρ : Δ ≤ Γ) : arr' Δ A⟨ρ⟩ B⟨ρ⟩ = (arr' Γ A B)⟨ρ⟩.
Proof. rewrite <- wk_prod. f_equal. eapply wk_up_wk1. Qed.

Lemma wk_lam {A t : term} {Γ Δ} (ρ : Δ ≤ Γ) : tLambda A⟨ρ⟩ t⟨wk_up A ρ⟩ = (tLambda A t)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_app {t u Γ Δ} (ρ : Δ ≤ Γ) : tApp t⟨ρ⟩ u⟨ρ⟩ = (tApp t u)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_sig {A B : term} {Γ Δ} (ρ : Δ ≤ Γ) : tSig A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tSig A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_pair {A B a b : term} {Γ Δ} (ρ : Δ ≤ Γ) : tPair A⟨ρ⟩ B⟨wk_up A ρ⟩ a⟨ρ⟩ b⟨ρ⟩ = (tPair A B a b)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_fst {p Γ Δ} (ρ : Δ ≤ Γ) : tFst p⟨ρ⟩ = (tFst p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_snd {p Γ Δ} (ρ : Δ ≤ Γ) : tSnd p⟨ρ⟩ = (tSnd p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_comp {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp A f g)⟨ρ⟩ = comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now bsimpl. Qed.
Notation comp' Γ A f g := (tLambda A (tApp f⟨@wk1 Γ (A : term)⟩ (tApp g⟨@wk1 Γ (A : term)⟩ (tRel 0)))).
Lemma wk_comp' {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp' Γ A f g)⟨ρ⟩ = comp' Δ A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof.
  rewrite <- wk_lam. f_equal. rewrite <- wk_app. f_equal. symmetry; eapply wk_up_wk1.
  rewrite <- wk_app. f_equal. symmetry; eapply wk_up_wk1.  Qed.

Lemma wk_emptyElim {Γ Δ P n} (ρ : Δ ≤ Γ) :
  tEmptyElim P⟨wk_up tEmpty ρ⟩ n⟨ρ⟩ = (tEmptyElim P n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_nSucc {n t Γ Δ} (ρ : Δ ≤ Γ) : (nSucc n t)⟨ρ⟩ = nSucc n t⟨ρ⟩.
Proof. unfold ren1, Ren1_well_wk. now rewrite (* nSucc_ren_alpha, *) nSucc_ren. Qed.
Lemma wk_nat_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (nat_to_term n)⟨ρ⟩ = nat_to_term n.
Proof. eapply (wk_nSucc (t:= tZero)). Qed.
Lemma wk_succ {n Γ Δ} (ρ : Δ ≤ Γ) : (tSucc n)⟨ρ⟩ = tSucc n⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; f_equal. now bsimpl.
Qed.
Lemma wk_elimSuccHypTy' {P Γ Δ} (ρ : Δ ≤ Γ) :
  elimSuccHypTy' Δ P⟨wk_up tNat ρ⟩ = (elimSuccHypTy' Γ P)⟨ρ⟩.
Proof.
  rewrite <- wk_prod, <- wk_arr'. f_equal. f_equal.
  erewrite (subst_ren_wk_up (wk_up tNat ρ)).
  f_equal. f_equal. change (wk_up tNat (@wk1 Δ tNat)) with (wk_up (tNat⟨ρ⟩ : term) (@wk1 Δ tNat)).
  now rewrite 2wk_comp_ren_on, wk_up_wk_comp, (wk_up_wk_comp (A:=tNat) ρ (wk1 tNat)),
   <- wk_up_wk1'.
Qed.
Lemma wk_natElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tNatElim P⟨wk_up tNat ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tNatElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_elimLeafHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimLeafHypTy P⟨wk_up A ρ⟩ = (elimLeafHypTy P)⟨ρ⟩.
Proof. unfold elimLeafHypTy; cbn. f_equal ; now bsimpl. Qed.
Lemma wk_elimLeafHypTy' {P Γ Δ} (ρ : Δ ≤ Γ) :
  elimLeafHypTy' Δ P⟨wk_up tTree ρ⟩ = (elimLeafHypTy' Γ P)⟨ρ⟩.
Proof.
  rewrite <- wk_prod. f_equal.
  erewrite (subst_ren_wk_up (* (A:= tTree⟨ρ⟩) *) (wk_up tNat ρ)). f_equal.
  change (wk_up tTree (@wk1 Δ tNat)) with (wk_up (tTree⟨ρ⟩ : term) (@wk1 Δ tNat)).
  now rewrite 2wk_comp_ren_on, wk_up_wk_comp, (wk_up_wk_comp (A:=tTree) ρ (wk1 tNat)),
    <- wk_up_wk1'.
Qed.

(* Lemma wk_elimNodeHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimNodeHypTy P⟨wk_up A ρ⟩ = (elimNodeHypTy P)⟨ρ⟩.
Proof. unfold elimNodeHypTy; cbn; f_equal; f_equal; f_equal; f_equal; [ | f_equal]; now bsimpl. Qed. *)
Lemma wk_elimNodeHypTyCod {P Γ Δ} (ρ : Δ ≤ Γ) (ρ' := wk_up tTree (wk_up tTree (wk_up tNat ρ))):
  elimNodeHypTyCod Δ P⟨wk_up tTree ρ'⟩ = (elimNodeHypTyCod Γ P)⟨ρ'⟩.
Proof.
  unfold elimNodeHypTyCod.
  etransitivity; [|eapply wk_arr'].
  etransitivity; [|eapply (f_equal (fun varP => arr' _ _ varP)), wk_arr'].
  eapply (f_equal2 tProd).
  { now rewrite (subst_ren_wk_up (A:=tTree)). }
  rewrite !wk1_ren_on.
  f_equal. eapply (f_equal2 (fun x y => arr x y)).
  all: now rewrite (subst_ren_wk_up (A:= tTree)).
Qed.

Lemma up_wk_up_wk1 {A B Γ Δ} {t : term} (ρ : Δ ≤ Γ) :
  t⟨wk_up A ρ⟩⟨wk_up A⟨ρ⟩ (@wk1 Δ B⟨ρ⟩)⟩ = t⟨wk_up A (@wk1 Γ B)⟩⟨wk_up A⟨@wk1 Γ B⟩ (wk_up B ρ)⟩.
Proof. rewrite 2 wk_comp_ren_on, 2 wk_up_wk_comp. now rewrite wk_up_wk1'. Qed.

Lemma wk_elimNodeHypTy' {P Γ Δ} (ρ : Δ ≤ Γ) :
  elimNodeHypTy' Δ P⟨wk_up tTree ρ⟩ = (elimNodeHypTy' Γ P)⟨ρ⟩.
Proof.
  unfold elimNodeHypTy'.
  etransitivity; [|eapply wk_prod]; f_equal.
  etransitivity; [|eapply wk_prod]; f_equal.
  etransitivity; [|eapply wk_prod]; f_equal.
  etransitivity; [|eapply wk_elimNodeHypTyCod]; f_equal.
  etransitivity.
  { eapply f_equal, f_equal, (up_wk_up_wk1 (B:=tNat)). }
  cbn. etransitivity.
  { eapply f_equal, (up_wk_up_wk1 (B:=tTree)). }
  cbn. eapply (up_wk_up_wk1 (B:=tTree)).
Qed.

(* Lemma elimNodeHypTy_to_typed {P Γ} : elimNodeHypTy' Γ P = elimNodeHypTy P.
Proof.
  unfold elimNodeHypTy.
  eapply (f_equal (tProd tNat)), (f_equal (tProd tTree)), (f_equal (tProd tTree)),
    f_equal2.
  1:{ rewrite wk1_ren_on; f_equal.
    apply up_wk1_ren_on. }
  rewrite wk1_ren_on.
  f_equal.
  eapply f_equal2.
  1:{ etransitivity; [apply up_wk1_ren_on|f_equal].
    apply up_wk1_ren_on. }
  rewrite wk1_ren_on. f_equal. f_equal.
  etransitivity; [apply up_wk1_ren_on|f_equal].
  etransitivity; [apply up_wk1_ren_on|f_equal].
  apply up_wk1_ren_on.
Qed.
Lemma wk_elimNodeHypTy' {P Γ Δ} (ρ : Δ ≤ Γ) :
  elimNodeHypTy' Δ P⟨wk_up tTree ρ⟩ = (elimNodeHypTy' Γ P)⟨ρ⟩.
Proof.
  rewrite 2elimNodeHypTy_to_typed.
  eapply wk_elimNodeHypTy.
Qed. *)

Lemma wk_treeElim {Γ Δ P hl hn t} (ρ : Δ ≤ Γ) :
  tTreeElim P⟨wk_up tTree ρ⟩ hl⟨ρ⟩ hn⟨ρ⟩ t⟨ρ⟩ = (tTreeElim P hl hn t)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_bool_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (bool_to_term n)⟨ρ⟩ = bool_to_term n.
Proof. unfold ren1, Ren1_well_wk. now rewrite bool_to_term_ren. Qed.
Lemma wk_boolElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tBoolElim P⟨wk_up tBool ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tBoolElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_Id {A x y Γ Δ} (ρ : Δ ≤ Γ) : tId A⟨ρ⟩ x⟨ρ⟩ y⟨ρ⟩ = (tId A x y)⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_refl {A x Γ Δ} (ρ : Δ ≤ Γ) : tRefl A⟨ρ⟩ x⟨ρ⟩ = (tRefl A x)⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_idElim {A x P hr y e : term}  {Δ Γ} (ρ : Δ ≤ Γ) :
  tIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨wk_up (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) (wk_up A ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩ = (tIdElim A x P hr y e)⟨ρ⟩.
Proof. reflexivity. Qed.


Lemma subst_arr' {A B Γ Δ} (σ : nat -> term) : arr' Δ A[σ] B[σ] = (arr' Γ A B)[σ].
Proof. cbn. f_equal. now rewrite 2wk1_ren_on, shift_up_eq. Qed.



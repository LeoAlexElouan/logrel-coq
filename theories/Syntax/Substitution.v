
From LogRel Require Import Utils AutoSubst.Extra Notations.
From LogRel.Syntax Require Import BasicAst Context NormalForms Computations Weakening.

Definition to_subst σ : substitution := mk_subst σ (fun n => n).
Lemma to_subst_sound t σ : t[σ] = t[to_subst σ].
Proof. now bsimpl. Qed.
Lemma up_to_subst σ: to_subst (up_term_term σ) = up_subst (to_subst σ).
Proof. reflexivity. Qed.

Definition wk_subst_comp {Γ Δ} (ρ : Δ ≤ Γ) σ : substitution := 
  mk_subst (fun x => (ρ >> (subst_subst σ)) x) (fun x => (ρ.(Fwk) >> (subst_alpha σ)) x).
Notation "ρ >>s σ" := (wk_subst_comp ρ σ) (at level 50).


Lemma wk_subst_comp_on {Γ Δ} (ρ : Δ ≤ Γ) σ (t : term) : t⟨ρ⟩[σ] = t[ρ >>s σ].
Proof. unfold wk_subst_comp. now bsimpl. Qed.

(* Definition wk_to_subst {Γ Δ} (ρ : Δ ≤ Γ) : substitution :=
  mk_subst (ρ.(wk) >> tRel) ρ.(Fwk). *)

(* Lemma wk_to_subst_sound {Γ Δ} (ρ : Δ ≤ Γ) (t : term) : t⟨ρ⟩ = t[wk_to_subst ρ]. *)


Lemma subst_ren_subst_up P n (σ : substitution) :
  P[n..][σ] = P[up_subst σ][(n[σ])..].
Proof. now bsimpl. Qed.


Lemma subst_up_wk1 {A Γ Δ} {t : term} (σ : substitution) :
   t[σ]⟨@wk1 Δ A[σ]⟩ = t⟨@wk1 Γ A⟩[up_subst σ].
Proof. rewrite 2wk1_ren_on. now bsimpl. Qed.

Lemma subst_prod {A B} (σ : substitution) : tProd A[σ] B[up_subst σ] = (tProd A B)[σ].
Proof. reflexivity. Qed.

(* Lemma wk_arr {A B Γ Δ} (ρ : Δ ≤ Γ) : arr A⟨ρ⟩ B⟨ρ⟩ = (arr A B)⟨ρ⟩.
Proof. now bsimpl. Qed. *)
Lemma subst_arr' {A B Γ Δ} (σ : substitution) : arr' Δ A[σ] B[σ] = (arr' Γ A B)[σ].
Proof. rewrite <- subst_prod. f_equal. eapply subst_up_wk1. Qed.

Lemma subst_lam {A t} (σ : substitution) : tLambda A[σ] t[up_subst σ] = (tLambda A t)[σ].
Proof. reflexivity. Qed.

(* Lemma wk_app {t u Γ Δ} (ρ : Δ ≤ Γ) : tApp t⟨ρ⟩ u⟨ρ⟩ = (tApp t u)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_sig {A B Γ Δ} (ρ : Δ ≤ Γ) : tSig A⟨ρ⟩ B⟨wk_up A ρ⟩ = (tSig A B)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_pair {A B a b Γ Δ} (ρ : Δ ≤ Γ) : tPair A⟨ρ⟩ B⟨wk_up A ρ⟩ a⟨ρ⟩ b⟨ρ⟩ = (tPair A B a b)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_fst {p Γ Δ} (ρ : Δ ≤ Γ) : tFst p⟨ρ⟩ = (tFst p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_snd {p Γ Δ} (ρ : Δ ≤ Γ) : tSnd p⟨ρ⟩ = (tSnd p)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_comp {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp A f g)⟨ρ⟩ = comp A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now bsimpl. Qed.
Notation comp' Γ A f g := (tLambda A (tApp f⟨@wk1 Γ A⟩ (tApp g⟨@wk1 Γ A⟩ (tRel 0)))).
Lemma wk_comp' {Γ Δ A f g} (ρ : Δ ≤ Γ) : (comp' Γ A f g)⟨ρ⟩ = comp' Δ A⟨ρ⟩ f⟨ρ⟩ g⟨ρ⟩.
Proof. now rewrite 2wk_up_wk1. Qed.

Lemma wk_emptyElim {Γ Δ P n} (ρ : Δ ≤ Γ) :
  tEmptyElim P⟨wk_up tEmpty ρ⟩ n⟨ρ⟩ = (tEmptyElim P n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_nSucc {n t Γ Δ} (ρ : Δ ≤ Γ) : (nSucc n t)⟨ρ⟩ = nSucc n t⟨ρ⟩.
Proof. unfold ren1, Ren1_well_wk. now rewrite nSucc_ren_alpha, nSucc_ren. Qed.
Lemma wk_nat_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (nat_to_term n)⟨ρ⟩ = nat_to_term n.
Proof. eapply (wk_nSucc (t:= tZero)). Qed.
Lemma wk_succ {n Γ Δ} (ρ : Δ ≤ Γ) : (tSucc n)⟨ρ⟩ = tSucc n⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_elimSuccHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimSuccHypTy P⟨wk_up A ρ⟩ = (elimSuccHypTy P)⟨ρ⟩.
Proof.
  unfold elimSuccHypTy; cbn; f_equal; f_equal. now bsimpl.
Qed. *)
Lemma subst_elimSuccHypTy' {Γ P} (σ : substitution) :
  elimSuccHypTy' Γ P[up_subst σ] = (elimSuccHypTy' Γ P)[σ].
Proof.
  rewrite <- subst_prod, <- (subst_arr' (Δ:=Γ)). f_equal. f_equal.
  rewrite 2wk1_ren_on; f_equal.
  rewrite subst_ren_subst_up. f_equal.
  rewrite 2up_wk1_ren_on. now bsimpl.
Qed.
(* Lemma wk_natElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
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
  change (wk_up tTree (@wk1 Δ tNat)) with (wk_up tTree⟨ρ⟩ (@wk1 Δ tNat)).
  now rewrite 2wk_comp_ren_on, wk_up_wk_comp, (wk_up_wk_comp (A:=tTree) ρ (wk1 tNat)),
    <- wk_up_wk1'.
Qed.

Lemma wk_elimNodeHypTy {P Γ Δ} A (ρ : Δ ≤ Γ) :
  elimNodeHypTy P⟨wk_up A ρ⟩ = (elimNodeHypTy P)⟨ρ⟩.
Proof. unfold elimNodeHypTy; cbn; f_equal; f_equal; f_equal; f_equal; [ | f_equal]; now bsimpl. Qed.
Lemma elimNodeHypTy_to_typed {P Γ} : elimNodeHypTy' Γ P = elimNodeHypTy P.
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
Qed.

Lemma wk_treeElim {Γ Δ P hl hn t} (ρ : Δ ≤ Γ) :
  tTreeElim P⟨wk_up tTree ρ⟩ hl⟨ρ⟩ hn⟨ρ⟩ t⟨ρ⟩ = (tTreeElim P hl hn t)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_bool_to_term {n Γ Δ} (ρ : Δ ≤ Γ) : (bool_to_term n)⟨ρ⟩ = bool_to_term n.
Proof. unfold ren1, Ren1_well_wk. now rewrite bool_to_term_ren_alpha, bool_to_term_ren. Qed.
Lemma wk_boolElim {Γ Δ P hz hs n} (ρ : Δ ≤ Γ) :
  tBoolElim P⟨wk_up tBool ρ⟩ hz⟨ρ⟩ hs⟨ρ⟩ n⟨ρ⟩ = (tBoolElim P hz hs n)⟨ρ⟩.
Proof. reflexivity. Qed.

Lemma wk_Id {A x y Γ Δ} (ρ : Δ ≤ Γ) : tId A⟨ρ⟩ x⟨ρ⟩ y⟨ρ⟩ = (tId A x y)⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_refl {A x Γ Δ} (ρ : Δ ≤ Γ) : tRefl A⟨ρ⟩ x⟨ρ⟩ = (tRefl A x)⟨ρ⟩.
Proof. reflexivity. Qed.
Lemma wk_idElim {A x P hr y e Δ Γ} (ρ : Δ ≤ Γ) :
  tIdElim A⟨ρ⟩ x⟨ρ⟩ P⟨wk_up (tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) (wk_up A ρ)⟩ hr⟨ρ⟩ y⟨ρ⟩ e⟨ρ⟩ = (tIdElim A x P hr y e)⟨ρ⟩.
Proof. reflexivity. Qed. *)

Definition tail_subst σ : substitution := mk_subst (↑ >> subst_subst σ) (subst_alpha σ).
Definition εtail_subst σ : substitution := mk_subst (subst_subst σ) (↑ >> subst_alpha σ).
Lemma wk1_subst (t A : term) σ Γ : t⟨@wk1 Γ A⟩[σ] = t[tail_subst σ].
Proof. now bsimpl. Qed.

Definition subst_comp σ' σ : substitution := mk_subst (fun x => ((subst_subst σ x)[σ'])) ((subst_alpha σ) >> (subst_alpha σ')).
Notation "σ' ∘s σ " := (subst_comp σ' σ) (at level 50).
Definition subst_comp_on (t : term) (σ σ' : substitution) : t[σ][σ'] = t[σ' ∘s σ].
Proof. unfold subst_comp. now bsimpl. Qed.

Definition subst_id : substitution := mk_subst tRel (fun x => x).
Definition subst_id_on (t : term) : t = t[subst_id].
Proof. unfold subst_id. now bsimpl. Qed.

Record subst_eq σ σ' := {
  eq_subst : subst_subst σ =1 subst_subst σ' ;
  eq_alpha : subst_alpha σ =1 subst_alpha σ' ;
  }.
Notation " σ =s σ' " := (subst_eq σ σ') (at level 50).

  Lemma eta_up_single_subst σ : to_subst (subst_subst σ var_zero).. ∘s up_subst (tail_subst σ) =s σ.
  Proof. constructor; cbn; bsimpl; bsimpl; reflexivity. Qed.

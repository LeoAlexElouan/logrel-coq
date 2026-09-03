
From LogRel Require Import Utils AutoSubst.Extra Notations.
From LogRel.Syntax Require Import BasicAst Context NormalForms Computations Weakening WeakeningCompute.

Definition to_subst σ : substitution := mk_subst σ (fun n => n).
Lemma to_subst_sound t σ : t[σ] = t[to_subst σ].
Proof. now bsimpl. Qed.
Lemma up_to_subst σ: to_subst (up_term_term σ) = up_subst (to_subst σ).
Proof. reflexivity. Qed.

Definition wk_subst_comp {Γ Δ} (ρ : Δ ≤ Γ) σ : substitution := 
  mk_subst (ρ >> (subst_subst σ)) (ρ.(Fwk) >> (subst_alpha σ)).
Notation "σ ∘r ρ" := (wk_subst_comp ρ σ) (at level 49).


Lemma wk_subst_comp_on {Γ Δ} (ρ : Δ ≤ Γ) σ (t : term) : t⟨ρ⟩[σ] = t[σ ∘r ρ].
Proof. unfold wk_subst_comp. now bsimpl. Qed.


Definition tail_subst σ : substitution := mk_subst (↑ >> subst_subst σ) (subst_alpha σ).
Definition εtail_subst σ : substitution := mk_subst (subst_subst σ) (↑ >> subst_alpha σ).
Lemma wk1_subst (t A : term) σ Γ : t⟨@wk1 Γ A⟩[σ] = t[tail_subst σ].
Proof. now bsimpl. Qed.

Definition subst_comp σ' σ : substitution := mk_subst (fun x => ((subst_subst σ x)[σ'])) ((subst_alpha σ) >> (subst_alpha σ')).
Notation "σ' ∘s σ " := (subst_comp σ' σ) (at level 49).
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


From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Instance subst_eq_refl : Reflexive subst_eq.
Proof. now constructor. Qed.
Instance subst_eq_sym : Symmetric subst_eq.
Proof. intros ?? H; constructor; symmetry; apply H. Qed.
Instance subst_eq_trans : Transitive subst_eq.
Proof. intros ??? Hl Hr; constructor; etransitivity; first [apply Hl| apply Hr]. Qed.
Instance subst_eq_equiv : Equivalence subst_eq.
Proof.
  constructor.
  + eapply subst_eq_refl.
  + eapply subst_eq_sym.
  + eapply subst_eq_trans.
Qed.
Instance wk_eq_equiv {Γ Δ} : Equivalence (@wk_eq Γ Δ).
Proof.
  repeat constructor.
  1,2: destruct H; now symmetry.
  1,2: destruct H, H0; now etransitivity.
Qed.

Instance subst_eq_subst : Proper (subst_eq ==> `=1`) subst_subst := eq_subst.
Instance subst_eq_subst2 : Morphisms.Proper (Morphisms.respectful subst_eq (Morphisms.respectful eq eq)) subst_subst.
Proof. intros σ σ' eqσ n n' <-. now eapply subst_eq_subst. Qed.
Instance subst_eq_alpha : Proper (subst_eq ==> `=1`) subst_alpha := eq_alpha.
Instance subst_eq_alpha2 : Morphisms.Proper (Morphisms.respectful subst_eq (Morphisms.respectful eq eq)) subst_alpha.
Proof. intros σ σ' eqσ n n' <-. now eapply subst_eq_alpha. Qed.
Instance Build_subst_eq_eq : Proper (`=1` ==> `=1` ==> subst_eq) mk_subst.
Proof. intros σ σ' eqσ ρ ρ' eqρ. now constructor. Qed.
Lemma subst_eq_alpha' : Proper (subst_eq ==> `=1`) subst_alpha.
Proof. intros σ σ' eq. setoid_rewrite eq. reflexivity. Qed.


Instance subst_subst_eq : Proper (respectful subst_eq (respectful eq eq)) Subst_alpha. (*  σ =s σ' -> t[σ] = t[σ']. *)
Proof.
  intros σ σ' eq  t t' <-.
  unfold Subst_alpha, subst1, Subst_term.
  now rewrite eq.
Qed.

Instance ren_alpha_substitution_eq : Proper (`=1` ==> subst_eq ==> subst_eq) ren_alpha_substitution.
Proof.
  intros ρε ρε' eqρε σ σ' eqσ.
  eapply Build_subst_eq_eq, funcomp_morphism, subst_eq_alpha; tea.
  intros n. eapply ren_alpha_morphism, subst_eq_subst; tea.
Qed.

Lemma ren1_subst_eq : Proper (`=1` ==> subst_eq ==> subst_eq) ren1.
Proof.
  intros ρ ρ' eqρ(* [eqρ eqρε] *) σ σ' eqσ.
  unfold ren1, ren_substitution.
  eapply Build_subst_eq_eq, subst_eq_alpha; tea.
  intros n.
  eapply ren_term_morphism, subst_eq_subst; tea.
Qed.

Instance ren_subst_eq Γ Δ : Proper (@wk_eq Γ Δ ==> subst_eq ==> subst_eq) ren1.
Proof.
  intros ρ ρ' [eqρ eqρε] σ σ' eqσ.
  unfold ren1, wk_substitution.
  now apply ren1_subst_eq, ren_alpha_substitution_eq.
Qed.

Instance wk_subst_comp_eq {Γ Δ} : Proper (@wk_eq Γ Δ ==> subst_eq ==> subst_eq) wk_subst_comp.
Proof.
  intros ρ ρ' [ρe ρeε] σ σ' σe.
  unfold wk_subst_comp.
  now rewrite ρe, ρeε, σe.
Qed.

Instance tail_subst_eq : Proper (subst_eq ==> subst_eq) tail_subst.
Proof. intros σ σ' eq. unfold tail_subst. now rewrite eq. Qed.
Instance up_subst_eq : Proper (subst_eq ==> subst_eq) up_subst.
Proof. intros σ σ' eq. unfold up_subst. now rewrite eq. Qed.


Instance subst_comp_eq : Proper (subst_eq ==> subst_eq ==> subst_eq) subst_comp.
Proof.
  intros σ σ' eqσ τ τ' eqτ.
  eapply Build_subst_eq_eq;
   intros n; now rewrite eqσ, eqτ.
Qed.


Definition CnotCmorphism {A} {R : relation A} (m :A) : Proper R m -> CMorphisms.Proper R m := fun x => x.
(* Instance subst_eq_subst2 : CMorphisms.Proper (CMorphisms.respectful subst_eq (CMorphisms.respectful eq eq)) subst_subst.
intros σ σ' eqσ n n' <-. now eapply subst_eq_subst. Qed. *)
Ltac instantiate_ltac_variable ev term :=
  let H := fresh in
  pose ev as H;
  instantiate (1 := term) in (value of H);
  clear H.


Ltac to_prop_rel R :=
  match type of R with
  | CRelationClasses.crelation ?A => let H := fresh in eset (H := _ : relation A); unify H R
  end. 
Ltac change_proper := 
  match goal with
    |- CMorphisms.Proper (CMorphisms.respectful ?R (CMorphisms.respectful ?R' ?R'')) ?m =>
      try to_prop_rel R'; try to_prop_rel R'';
      change (Morphisms.Proper (respectful R (respectful R' R'')) m);
      apply CnotCmorphism
    | |- CMorphisms.Proper (CMorphisms.respectful ?R ?R') ?m =>
      try to_prop_rel R';
      change (Morphisms.Proper (respectful R R') m);
      apply CnotCmorphism
  end.

#[global] Hint Extern 10 (CMorphisms.Proper _ _) => change_proper : typeclass_instances.


Lemma wk1_tail {Γ A σ} : σ ∘r @wk1 Γ A =s tail_subst σ.
Proof. constructor; unfold wk_subst_comp; bsimpl; reflexivity. Qed.
Lemma tail_single_subst σ t : tail_subst (σ ∘s to_subst t..) = σ.
Proof. destruct σ as [σ ρ]. reflexivity. Qed.
Lemma eq_upwk {Γ Δ} A σ (ρ : Δ ≤ Γ) : (up_subst σ)⟨wk_up A ρ⟩ =s (up_subst σ⟨ρ⟩).
Proof.
  eapply Build_subst_eq_eq, Equivalence.pointwise_equivalence, eq_equivalence.
  cbn. intros [].
  + cbv. reflexivity.
  + bsimpl. unfold funcomp. now bsimpl.
Qed.

Lemma eta_subst σ σ' : subst_subst σ var_zero = subst_subst σ' var_zero -> tail_subst σ =s tail_subst σ' -> σ  =s σ'.
Proof.
  intros eh [et eεt].
  constructor.
  + intros [].
    - eapply eh.
    - eapply (et n).
  + eapply eεt.
Qed.

Lemma tail_subst_comp {σ τ} : tail_subst (τ ∘s σ) = τ ∘s (tail_subst σ).
Proof. reflexivity. Qed.
Lemma tail_to_subst {t σ} : tail_subst (to_subst t.. ∘s up_subst σ) =s σ.
Proof. constructor; cbn; [|reflexivity]; bsimpl; bsimpl; reflexivity. Qed.
Lemma eta_up_single_subst σ : to_subst (subst_subst σ var_zero).. ∘s up_subst (tail_subst σ) =s σ.
Proof. eapply eta_subst. {reflexivity. } eapply tail_to_subst. Qed.
(* Lemma tail_up_subst {Γ A σ} : tail_subst (up_subst σ) = σ ∘r @wk1 Γ A.
Proof. reflexivity. Qed. *)

Lemma wk_up_wk1_subst σ Γ A : σ⟨@wk1 Γ A⟩ =s up_subst σ ∘r (@wk1 Γ A).
Proof.
  unfold wk_subst_comp, up_subst. cbn. bsimpl.
  constructor.
  + cbn. bsimpl. intros n. cbn. now bsimpl.
  + cbn. now bsimpl.
Qed.

Generalizable All Variables.
  Lemma up_subst_comp {σ τ} : up_subst (σ ∘s τ) =s (up_subst σ ∘s up_subst τ).
  Proof.
    constructor.
    + intros [].
      { reflexivity. }
      cbn; now bsimpl.
    + reflexivity.
  Qed.
  Lemma up_subst_id : up_subst subst_id =s subst_id.
  Proof.
    repeat constructor.
    intros []; reflexivity.
  Qed.
  Lemma tail_scons {t} : tail_subst (to_subst t..) =s subst_id.
  Proof.
    constructor.
    + cbn. now bsimpl.
    + reflexivity.
  Qed.
Lemma wk_up_subst σ A `(ρ : Ξ ≤ Δ) : up_subst σ ∘r wk_up A ρ =s up_subst (σ ∘r ρ).
Proof.
  constructor.
  + intros []; reflexivity.
  + reflexivity.
Qed.

Lemma subst_ren_subst_up P n (σ : substitution) :
  P[n..][σ] = P[up_subst σ][(n[σ])..].
Proof. now bsimpl. Qed.

Lemma subst_ren_wk {Γ Δ} {A : term} {σ : substitution} (ρ : Δ ≤ Γ) : A[σ]⟨ρ⟩ = A[σ⟨ρ⟩] :> term.
Proof. now bsimpl. Qed.
Lemma subst_up_wk1 {A : term} {Γ Δ : context} {t : term} (σ : substitution) :
   t[σ]⟨@wk1 Δ (A[σ] : term)⟩ =  t⟨@wk1 Γ A⟩[up_subst σ] :> term.
Proof. rewrite 2wk1_ren_on. now bsimpl. Qed.
Lemma up_subst_wk_up_wk1 {A B Γ Δ} {t : term} (σ : substitution) :
  t[up_subst σ]⟨wk_up A[σ] (@wk1 Δ B[σ])⟩ = t⟨wk_up A (@wk1 Γ B)⟩[up_subst (up_subst σ)].
Proof. rewrite !up_wk1_ren_on. now bsimpl. Qed.

Lemma up_subst_wk1 Γ Δ A B t σ :
  t[up_subst σ⟨@wk1 Γ A⟩] = t⟨wk_up B (@wk1 Δ A)⟩[up_subst (up_subst σ)].
Proof. now unshelve now erewrite <- eq_upwk, <- subst_ren_wk, <- up_subst_wk_up_wk1, 2 up_wk1_ren_on. Qed.

Lemma subst_prod {A B} (σ : substitution) : tProd A[σ] B[up_subst σ] = (tProd A B)[σ].
Proof. reflexivity. Qed.
Lemma subst_arr' {A B Γ Δ} (σ : substitution) : arr' Δ A[σ] B[σ] = (arr' Γ A B)[σ].
Proof. rewrite <- subst_prod. f_equal. eapply subst_up_wk1. Qed.
Lemma subst_lam {A t} (σ : substitution) : tLambda A[σ] t[up_subst σ] = (tLambda A t)[σ].
Proof. reflexivity. Qed.
Lemma subst_app {t u} (σ : substitution) : tApp t[σ] u[σ] = (tApp t u)[σ].
Proof. reflexivity. Qed.

Lemma subst_sig {A B} (σ : substitution) : tSig A[σ] B[up_subst σ] = (tSig A B)[σ].
Proof. reflexivity. Qed.
Lemma subst_pair {A B a b} (σ : substitution) : tPair A[σ] B[up_subst σ] a[σ] b[σ] = (tPair A B a b)[σ].
Proof. reflexivity. Qed.
Lemma subst_fst {p} (σ : substitution) : tFst p[σ] = (tFst p)[σ].
Proof. reflexivity. Qed.
Lemma subst_snd {p} (σ : substitution) : tSnd p[σ] = (tSnd p)[σ].
Proof. reflexivity. Qed.


Lemma subst_bool_to_term {n} (σ : substitution) : (bool_to_term n)[σ] = bool_to_term n.
Proof. destruct n; reflexivity. Qed.
Lemma subst_boolElim {P hz hs n} (σ : substitution) :
  tBoolElim P[up_subst σ] hz[σ] hs[σ] n[σ] = (tBoolElim P hz hs n)[σ].
Proof. reflexivity. Qed.


Lemma subst_nSucc {n t} (σ : substitution) : (nSucc n t)[σ] = nSucc n t[σ].
Proof. induction n; [reflexivity|]. eapply (f_equal tSucc IHn). Qed.
Lemma subst_nat_to_term {n} (σ : substitution) : (nat_to_term n)[σ] = nat_to_term n.
Proof. eapply (subst_nSucc (t:=tZero)). Qed.
Lemma subst_elimSuccHypTy' {Γ Δ P} (σ : substitution) :
  elimSuccHypTy' Δ P[up_subst σ] = (elimSuccHypTy' Γ P)[σ].
Proof.
  rewrite <- subst_prod, <- (subst_arr' (Δ:=Γ)). f_equal. f_equal.
  rewrite 2wk1_ren_on; f_equal.
  rewrite subst_ren_subst_up. f_equal.
  eapply up_subst_wk_up_wk1.
Qed.
Lemma subst_natElim {P hz hs n} (σ : substitution) :
  tNatElim P[up_subst σ] hz[σ] hs[σ] n[σ] = (tNatElim P hz hs n)[σ].
Proof. reflexivity. Qed.

Lemma subst_elimLeafHypTy' {Γ Δ P} (σ : substitution) :
  elimLeafHypTy' Δ P[up_subst σ] = (elimLeafHypTy' Γ P)[σ].
Proof.
  rewrite <- subst_prod. f_equal.
  rewrite subst_ren_subst_up. f_equal.
  eapply up_subst_wk_up_wk1.
Qed.

Lemma subst_elimNodeHypTyCod {P Γ Δ} (σ : substitution) (σ' := up_subst (up_subst (up_subst σ))):
  elimNodeHypTyCod Δ P[up_subst σ'] = (elimNodeHypTyCod Γ P)[σ'].
Proof.
  unfold elimNodeHypTyCod.
  erewrite <-2 subst_arr'. f_equal.
  { now rewrite subst_ren_subst_up. }
  erewrite wk1_irr. f_equal. f_equal.
  { now rewrite subst_ren_subst_up. }
  erewrite wk1_irr. f_equal.
  { now rewrite subst_ren_subst_up. }
  Unshelve. all: tea.
Qed.

Lemma subst_elimNodeHypTy' {Γ Δ P} (σ : substitution) :
  elimNodeHypTy' Δ P[up_subst σ] = (elimNodeHypTy' Γ P)[σ].
Proof.
  unfold elimNodeHypTy'.
  rewrite <- 3subst_prod. do 3 f_equal.
  erewrite <- subst_elimNodeHypTyCod.
  f_equal.
  etransitivity; [|eapply up_subst_wk_up_wk1].
  f_equal.
  etransitivity; [|eapply up_subst_wk_up_wk1].
  f_equal.
  eapply up_subst_wk_up_wk1.
Qed.

Lemma subst_treeElim {P hl hn t} (σ : substitution) :
  tTreeElim P[up_subst σ] hl[σ] hn[σ] t[σ] = (tTreeElim P hl hn t)[σ].
Proof. reflexivity. Qed.

Lemma subst_xi {ℓ t} (σ : substitution) : tXi ℓ t[up_subst σ] = (tXi ℓ t)[σ].
Proof. reflexivity. Qed.
Lemma subst_xxi {ℓ t u } (σ : substitution) : tXXi ℓ t[up_subst σ] u[σ] = (tXXi ℓ t u)[σ].
Proof. reflexivity. Qed.
Lemma subst_eval {ℓ t} (σ : substitution) : tEval ℓ t[σ] = (tEval ℓ t)[σ].
Proof. reflexivity. Qed.
Lemma subst_box {ℓ t} (σ : substitution) : tBox ℓ t[σ] = (tBox ℓ t)[σ].
Proof. reflexivity. Qed.

Lemma subst_ellElim {ℓ k P ht hf n b} (ℓt := cons_ell ℓ k true) (ℓf := cons_ell ℓ k false) (σ : substitution):
  tEllElim k ℓ P[up_subst σ] ht[up_subst σ] hf[up_subst σ] n[σ] b[σ] = (tEllElim k ℓ P ht hf n b)[σ].
Proof. reflexivity. Qed.

Lemma subst_decl {t} (σ : substitution) : term_decl t[σ] = (term_decl t)[σ].
Proof. reflexivity. Qed.
Lemma subst_ell {ℓ} (σ : substitution) : ell_decl ℓ = (ell_decl ℓ)[σ].
Proof. reflexivity. Qed.

Lemma subst_dEvalNode' {Γ Δ n} (σ : substitution) :
  dEvalNode' Δ n[σ] = (dEvalNode' Γ n)[σ].
Proof.
  unfold dEvalNode'.
  do 5 (rewrite <- subst_lam; eapply (f_equal (fun x => tLambda _ x))).
  rewrite <- subst_boolElim; eapply (f_equal (fun x => tBoolElim _ _ _ x)).
  rewrite <- subst_app; eapply (f_equal (fun x => tApp x _)).
  now do 5 (etransitivity; [ eapply (f_equal (fun x => x⟨@wk1 _ _⟩))| refine (subst_up_wk1 _)]).
Qed.
Lemma subst_dEval' {Γ Δ d n} (σ : substitution) :
  dEval' Δ d[σ] n[σ] = (dEval' Γ d n)[σ].
Proof.
  unfold dEval'. (* cbn. repeat f_equal. now bsimpl. *)
  rewrite <- subst_treeElim; f_equal.
  eapply subst_dEvalNode'.
Qed.


Lemma subst_leaf {t} {σ : substitution} : tLeaf t[σ] = (tLeaf t)[σ].
Proof. reflexivity. Qed.
Lemma subst_node {t dl dr} {σ : substitution} : tNode t[σ] dl[σ] dr[σ] = (tNode t dl dr)[σ].
Proof. reflexivity. Qed.
Lemma subst_Id {A x y} {σ : substitution} : tId A[σ] x[σ] y[σ] = (tId A x y)[σ].
Proof. reflexivity. Qed.
Lemma subst_refl {A x} {σ : substitution} : tRefl A[σ] x[σ] = (tRefl A x)[σ].
Proof. reflexivity. Qed.























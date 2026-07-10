From Stdlib Require Import ssreflect Morphisms Setoid.
From LogRel Require Import Utils BasicAst AutoSubst.Extra.

Set Primitive Projections.

Fixpoint nSucc n t : term :=
  match n with
  | 0 => t
  | S n => tSucc (nSucc n t)
  end.

Definition nat_to_term n : term :=
  nSucc n tZero.

Definition bool_to_term b : term :=
  match b with
  | true => tTrue
  | false => tFalse
  end.

Lemma bool_to_term_ren : forall b ρ, (bool_to_term b)⟨ρ⟩ = bool_to_term b.
Proof.
  intros [|] ρ; reflexivity.
Qed.
Lemma bool_to_term_ren_alpha : forall b ρε, ren_alpha ρε (bool_to_term b) = bool_to_term b.
Proof.
  intros [|] ρ; reflexivity.
Qed.


Lemma nSucc_ren : forall n t ρ, (nSucc n t)⟨ρ⟩ = nSucc n (t⟨ρ⟩).
Proof.
  intros n t ρ.
  induction n; cbn.
  - reflexivity.
  - now f_equal.
Qed.
Lemma nSucc_ren_alpha : forall n t ρε, ren_alpha ρε (nSucc n t) = nSucc n (ren_alpha ρε t).
Proof.
  intros n t ρ.
  induction n; cbn.
  - reflexivity.
  - now f_equal.
Qed.
Lemma nSucc_subst : forall {n t σ}, nSucc n t[σ] = (nSucc n t)[σ].
Proof.
  intros n t σ.
  induction n; cbn.
  - reflexivity.
  - now f_equal.
Qed.

Lemma nat_to_term_ren : forall n ρ, (nat_to_term n)⟨ρ⟩ = nat_to_term n.
Proof.
  intros n ρ.
  eapply nSucc_ren.
Qed.
Lemma nat_to_term_ren_alpha : forall n ρε, ren_alpha ρε (nat_to_term n) = nat_to_term n.
Proof.
  intros n ρ.
  eapply nSucc_ren_alpha.
Qed.
Lemma nat_to_term_subst : forall n σ, nat_to_term n = (nat_to_term n)[σ].
Proof.
  intros n σ.
  eapply @nSucc_subst with (t:=tZero).
Qed.

Lemma nat_to_term_inj {n n'} : nat_to_term n = nat_to_term n' -> n = n'.
Proof.
  revert n'.
  induction n.
  - intros n' e.
    destruct n'.
    + reflexivity.
    + inversion e.
  - intros [|] e.
    + inversion e.
    + inversion e; subst.
      f_equal.
      now apply IHn.
Qed.

Lemma nSucc_eq_inv {t t' k k'} : nSucc k t = nSucc k' t' -> (k = k'/\ t = t') \/
  (exists n', t = tSucc (nSucc n' t') /\ S (k + n') = k') \/
  (exists n, tSucc (nSucc n t) = t' /\ k = S (k' + n)).
Proof.
  induction k in k' |-*;
  destruct k'; cbn.
  - now intros <-.
  - intros ->.
    right; left.
    now exists k'.
  - intros <-.
    right; right.
    now exists k.
  - intros e; injection e; clear e.
    intros e.
    specialize (IHk _ e).
    destruct IHk as[[<- <-]| [(n'&->&<-)|(n&<-&->)]].
    + now left.
    + now right; left; exists n'.
    + now right; right; exists n.
Qed.


Lemma nSucc_nat_to_term t n k : nat_to_term n = nSucc k t -> exists k', nat_to_term k' = t.
Proof.
  induction k in n |-*.
  + now exists n.
  + destruct n; inversion 1.
    now eapply IHk.
Qed.

Lemma nSuccswap n t : nSucc n (tSucc t) = tSucc (nSucc n t).
Proof.
  induction n.
  + reflexivity.
  + cbn. now rewrite IHn.
Qed.

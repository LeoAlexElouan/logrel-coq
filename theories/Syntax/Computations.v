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

Lemma nSucc_ren : forall n t ρ, (nSucc n t)⟨ρ⟩ = nSucc n (t⟨ρ⟩).
Proof.
  intros n t ρ.
  induction n; cbn.
  - reflexivity.
  - now f_equal.
Qed.

Lemma nat_to_term_ren : forall n ρ, (nat_to_term n)⟨ρ⟩ = nat_to_term n.
Proof.
  intros n ρ.
  eapply nSucc_ren.
Qed.

Lemma nat_to_term_inj n n' : nat_to_term n = nat_to_term n' -> n = n'.
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
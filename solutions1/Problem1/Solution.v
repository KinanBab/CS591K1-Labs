Require Import Frap Helpers.

Require Import Problem.

Fixpoint fact (n: nat): nat :=
  match n with
  | 0 => 1
  | S n' => n * fact n'
  end.

Theorem fact_thm1:
  fact 5 = 120.
Proof.
  simplify.
  equality.
Qed.

Theorem fact_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact n = 2 * k).
Proof.
  simplify.
  induct n.
  * linear_arithmetic.
  * cases (n =? 1).
    - comparison_bool_to_prop.
      rewrite Heq.
      simplify.
      exists 1.
      linear_arithmetic.
    - comparison_bool_to_prop.
      assert (n > 1) by linear_arithmetic.
      propositional.
      clear H Heq H0.
      invert H1.
      exists (x * S n).
      simplify.
      rewrite H.
      ring.
Qed.

Fixpoint fact_CPS (n: nat) (C: nat -> nat): nat :=
  match n with
  | 0 => C 1
  | S n' => fact_CPS n' (fun R => C (n * R))
  end.

Theorem CPS_correct: forall (n: nat) (f: nat -> nat),
 fact_CPS n f = f (fact n).
Proof.
  induct n; simplify.
  + trivial.
  + apply IHn with (f := fun R: nat => f ( S n * R )).
Qed.

Theorem fact_CPS_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact_CPS n (fun R => R) = 2 * k).
Proof.
  simplify.
  rewrite CPS_correct.
  apply fact_thm2.
  assumption.
Qed.

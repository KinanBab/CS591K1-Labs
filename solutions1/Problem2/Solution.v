Require Import Frap Modeling Helpers.

Require Import Problem.

Fixpoint fib (n: nat) : nat :=
  match n with
  | 0 => 1
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end
  end.

Lemma fib_iterative_buildup: forall (n: nat) (v: valuation),
  repeat_interpreter (S n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "pre" =
  repeat_interpreter (n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur".
Proof.
  simplify; equality.
Qed.

Lemma fib_iterative_loop_correct: forall (n: nat) (v: valuation),
  repeat_interpreter n fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur" = fib n.
Proof.
  simplify.
  strong_induct n.
  - simplify.  trivial.
  - simplify.
    cases n.
    * simplify. trivial.
    * assert (HA := H).
      specialize H with (n0 := S n).
      specialize HA with (n0 := n).
      assert (S n < S (S n)) by linear_arithmetic.
      assert (n < S (S n)) by linear_arithmetic.
      apply H in H0. apply HA in H1.
      clear H HA.
      rewrite H0. clear H0.
      rewrite fib_iterative_buildup.
      rewrite H1.
      linear_arithmetic.
Qed.

Theorem fib_iterative_correct': forall (n: nat) (v: valuation),
  (interpret' (fib_iterative n) v) $! "ret_" = fib n.
Proof.
  simplify.
  apply fib_iterative_loop_correct.
Qed.

Theorem fib_iterative_correct: forall (n: nat),
  interpret (fib_iterative n) = fib n.
Proof.
  simplify.
  unfold interpret.
  apply fib_iterative_correct'.
Qed.
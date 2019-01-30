(* I suggest you start by reading the comments and some of the definitions in Modeling.v
   Then reading the problem statement and hints in Problem.v *)
Require Import Frap Modeling Helpers.
Require Import Problem.

(* Start by implementing fibonacci recursively. *)
Fixpoint fib (n: nat) : nat := 0.

(* You are not required to prove these lemmas, but they will help you prove the main theorem.
   If you are stuck, use admit and Admitted to skip certain parts of the proofs or certain lemmas.
   You will still be able to use skipped lemmas during other proofs *)
Lemma fib_iterative_buildup: forall (n: nat) (v: valuation),
  repeat_interpreter (S n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "pre" =
  repeat_interpreter (n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur".
Proof.
Admitted.

Lemma fib_iterative_loop_correct: forall (n: nat) (v: valuation),
  repeat_interpreter n fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur" = fib n.
Proof.
Admitted.

Lemma fib_iterative_correct': forall (n: nat) (v: valuation),
  (interpret' (fib_iterative n) v) $! "ret_" = fib n.
Proof.
Admitted.

(* Main theorem: Prove this for full credit *)
Theorem fib_iterative_correct: forall (n: nat),
  interpret (fib_iterative n) = fib n.
Proof.
Admitted.

Require Import Frap Imperative Hoare Examples.

(* Swapping *)
Theorem swap_correct : forall a b,
  {{ fun h v => v $! "x" = a /\ v $! "y" = b}}
  swap_program
  {{ fun h v => v $! "x" = b /\ v $! "y" = a}}.
Proof.
  simplify.
  eapply HtSeq.
  apply HtAssign.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  apply HtAssign.
  simplify.
  t.
Restart.
  ht.
Qed.

(* Max *)
Theorem max_ok : forall a b,
  {{ fun h v => v $! "x" = a /\ v $! "y" = b}}
  max_program
  {{ fun h v =>  v $! "m" = Nat.max a b}}.
Proof.
  simplify.
  eapply HtStrengthenPost.
  apply HtIf.
  apply HtAssign.
  apply HtAssign.
  simplify.
  t.
Restart.
  ht.
Qed.

(* Factorial *)
Definition fact_invariant (n: nat) (h: heap) (v: valuation) : Prop :=
  (v $! "acc") * fact (v $! "n") = fact n.

Theorem fact_ok : forall n,
  {{ fun h v => v $! "n" = n}}
  fact_program (fact_invariant n)
  {{ fun h v =>  v $! "acc" = fact n}}.
Proof.
  unfold fact_program.
  unfold fact_invariant.

  simplify.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  eapply HtWhile.
  simplify.
  t.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  apply HtAssign.
  simplify.
  t.

  + rewrite fact_rec in H0.
    - ring [H0].
    - linear_arithmetic.
  + simplify.
    t.
    rewrite fact_base in H0.
    - t.
    - linear_arithmetic.
Restart.
  unfold fact_program.
  unfold fact_invariant.

  simplify.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  eapply HtWhile.
  simplify.
  t.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  apply HtAssign.
  simplify.
  t.

  Hint Rewrite fact_base fact_rec using linear_arithmetic.
  simplify.

  ring [H0].
  simplify.
  t.
Restart.
  Hint Rewrite fact_base fact_rec using linear_arithmetic.
  unfold fact_program.
  unfold fact_invariant.
  ht.
  ring [H0].
Qed.



Require Import Frap.

(* Helpful lemma to prove validity of strong induction *)
Lemma strengthen_strong_induction : forall P,
    (forall m, (forall n, n < m -> P n) -> P m) ->
    forall n, (forall m, m <= n -> P m).
Proof.
  induct n.
  + simplify.
    assert (m = 0) by linear_arithmetic.
    rewrite H0 in *.
    apply X.
    simplify.
    linear_arithmetic.
  + simplify.
    apply X.
    simplify.
    apply IHn.
    linear_arithmetic.
Qed.

(* Principle of strong induction is a valid way to prove any
   proposition about natural numbers. *)
Theorem strong_induction_valid : forall P : nat -> Prop,
  (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
  forall n : nat, P n.
Proof.
  simplify.
  pose strengthen_strong_induction.
  specialize p with (P := P).
  propositional.
  specialize H0 with (n := S n) (m := n).
  apply H0.
  linear_arithmetic.
Qed.

(* Our strong induction tactic, pass it n: the natural number 
   on which to do strong induction, and it will spit out two goals:
   a base case (n = 0), and an inductive step with a strong inductive 
   hypothesis. *)
Ltac strong_induct n :=
  induction n using strong_induction_valid; cases n.
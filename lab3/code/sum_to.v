Require Import Frap.

(* Sum to and CPS *)
Fixpoint sum_to (n: nat): nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_to n'
  end.

Theorem sum_to_thm : forall (n: nat),
  2 * sum_to n = n * (n+1).
Proof.
  induct n.
  + simplify; linear_arithmetic.
  + assert (2 * sum_to (S n) = 2 * (S n) + 2 * sum_to n) by (simplify; ring).
    rewrite H.
    rewrite IHn.
    clear H IHn.
    ring.
Qed.

Fixpoint sum_to_CPS (n: nat) (C: nat -> nat): nat :=
  match n with
  | 0 => C 0
  | S n' => sum_to_CPS n' (fun R => C (n + R))
  end.

Theorem CPS_correct: forall (n: nat) (f: nat -> nat),
  f (sum_to n) = sum_to_CPS n f.
Proof.
  induct n; simplify.
  + trivial.
  + apply IHn with (f := fun R: nat => f (S (n + R))).
Qed.

Theorem sum_to_thm2: forall (n: nat),
  2 * (sum_to_CPS n (fun R: nat => R)) = n * (n + 1).
Proof.
  simplify.
  pose CPS_correct.
  symmetry in e.
  rewrite e with (n := n) (f := fun R: nat => R).
  apply sum_to_thm.
Qed.
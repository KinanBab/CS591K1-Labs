Require Import Frap Helpers.

Require Import Problem.

Fixpoint fact (n: nat): nat :=
  0 (* Part 1: Implement this *)
.

Theorem fact_thm1:
  fact 5 = 120.
Proof.
  (* Part 1: Prove this after implementing fact *)
Admitted.

Theorem fact_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact n = 2 * k).
Proof.
  (* Part 2: Prove this after implementing fact *)
Admitted.

Fixpoint fact_CPS (n: nat) (C: nat -> nat): nat :=
  (* Part 3: Implement factorial using continuation passing style
     C is the continuation *)
  C 0.

Theorem CPS_correct: forall (n: nat) (f: nat -> nat),
 fact_CPS n f = f (fact n).
Proof.
  (* Part 3: Prove factorial using continuation passing style is correct *)
Admitted.

Theorem fact_CPS_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact_CPS n (fun R => R) = 2 * k).
Proof.
  (* Part 4: Freeby: Prove this using CPS_correct and fact_thm2! *)
Admitted.
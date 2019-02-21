Module Type Problem1.
  Parameter fact: nat -> nat.

  Axiom fact_thm1:
    fact 5 = 120.

  Axiom fact_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact n = 2 * k).

  Parameter fact_CPS: nat -> (nat -> nat) -> nat.

  Axiom CPS_correct: forall (n: nat) (f: nat -> nat),
    fact_CPS n f = f (fact n).

  Axiom fact_CPS_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact_CPS n (fun R => R) = 2 * k).
End Problem1.

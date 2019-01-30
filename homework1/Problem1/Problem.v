Module Type Problem1.
  Parameter fact: nat -> nat.

  (* Freeby! *)
  Axiom fact_thm1:
    fact 5 = 120.

  (* Prove that factorial of any number greater than 1 is even *)
  (* HINT: use induction! *)
  Axiom fact_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact n = 2 * k).

  Parameter fact_CPS: nat -> (nat -> nat) -> nat.

  (* Prove that your contiuation-passing-style implemenation is
     equivalent to the regular implementation *)
  Axiom CPS_correct: forall (n: nat) (f: nat -> nat),
    fact_CPS n f = f (fact n).

  (* An easy way to prove this is to put CPS_Correct and fact_thm2 together ;) *)
  Axiom fact_CPS_thm2: forall (n: nat),
  n > 1 -> (exists (k: nat), fact_CPS n (fun R => R) = 2 * k).
End Problem1.

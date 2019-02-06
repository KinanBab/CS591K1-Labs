Require Import Program Omega Ring ArithRing List.

Program Fixpoint sum_to (n: nat): {r: nat | 2 * r = n * (n+1) } :=
  match n with
  | 0 => 0
  | S n' => n + sum_to n'
  end.

Check sum_to_obligation_1.
Obligation 2 of sum_to.
  simpl.
  assert (S (n' + x + S (n' + x + 0)) = n' + (x + (x + 0)) + n' + 2) by omega.
  rewrite H. clear H.
  rewrite e. clear e.
  ring.
Defined sum_to.




Locate "|".
Check sig.
Print sig.
(* Look here https://coq.inria.fr/library/Coq.Init.Specif.html *)
Check exist.
Check existT.


Program Fixpoint my_reverse (A: Type) (l: list A): {l': list A | length l = length l'} :=
  match l with
  | nil => nil
  | cons head tail => (my_reverse A tail) ++ [head]
  end.
Obligation 2 of my_reverse.
  Search (length (_ ++ _) = length _ + length _).
  rewrite app_length.
  simpl.
  omega.
Defined my_reverse.
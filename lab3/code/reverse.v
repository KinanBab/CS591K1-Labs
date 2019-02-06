Require Import Frap.

(* Levels of verification *)
Fixpoint my_reverse (A: Type) (l: list A): list A :=
  match l with
  | nil => nil
  | cons head tail => app (my_reverse A tail) (cons head nil)
  end.

Arguments my_reverse [A].

Theorem my_reverse_correct1: forall (A: Type) (l: list A),
  length l = length (my_reverse l).
Proof.
  simplify.
  induct l.
  + simplify. trivial.
  + simplify.
    rewrite IHl.
    Search (length (_ ++ _) = length _ + length _).
    (* https://coq.inria.fr/library/Coq.Lists.List.html *)
    rewrite app_length.
    simplify.
    linear_arithmetic.
Qed.

Theorem my_reverse_correct2: forall (A: Type) (l: list A),
  length l = length (my_reverse l) /\
  (forall (e: A), (In e l) -> In e (my_reverse l)) /\
  (forall (e: A), (In e (my_reverse l)) -> In e l).
Proof.
  simplify.
  propositional.
  + apply my_reverse_correct1.
  + induct l.
    - simplify. trivial.
    - simplify.
      Locate "\/".
      Print or.
      destruct H. (* alternatively invert from Frap *)
      * 
        Search (In _ _ \/ In _ _ -> In _ (_ ++ _)).
        apply in_or_app.
        simplify.
        propositional.
      * apply in_or_app.
        (* version 1: natural-deduction like *)
        apply or_introl.
        apply IHl.
        assumption.
        (* alternatively:
         apply IHl in H. propositional *)
  + induct l.
    - simplify. trivial.
    - simplify.
      Search (In _ (_ ++ _) -> In _ _ \/ In _ _).
      apply in_app_or in H.
      destruct H.
      * apply or_intror.
        apply IHl.
        assumption.
      * simplify.
        propositional.
Qed.

Theorem my_reverse_correct3: forall (A: Type) (l: list A),
  length l = length (my_reverse l) /\
  (forall (a: A), my_reverse [a] = [a]) /\
  forall (l1 l2: list A) (a1 a2: A),
    (my_reverse (l1 ++ [a1; a2] ++ l2)) = (my_reverse l2) ++ [a2; a1] ++ (my_reverse l1).
Proof.
  pose my_reverse_correct1.
  simplify.
  propositional.
  + apply e.
  + induct l1; induct l2; simplify.
    - equality.
    - Search ((_ ++ _) ++ _ = _ ++ (_ ++ _)).
      rewrite app_assoc_reverse.
      simplify.
      equality.
    - specialize IHl1 with (l2 := nil) (a1 := a1) (a2 := a2).
      rewrite IHl1.
      simplify.
      equality.
    - specialize IHl1 with (l2 := a0 :: l2).
      rewrite IHl1.
      simplify.
      rewrite app_assoc_reverse.
      simplify.
      equality.
Qed.

Search (nat -> list _ ->  _).
Search (list _ ->  nat -> _).
Theorem my_reverse_really_correct: forall (A: Type) (l: list A),
    length l = length (my_reverse l) /\
    forall (i: nat), i < length l -> nth_error l i = nth_error (my_reverse l) (length l - i - 1).
Proof.
  pose my_reverse_correct1.
  simplify.
  propositional.
  - apply e.
  - induct l.
    + simplify. linear_arithmetic.
    + cases i.
      -- simplify.
         rewrite nth_error_app2.
         ++ rewrite e with A l.
            assert (length (my_reverse l) - 0 - length (my_reverse l) = 0) by linear_arithmetic.
            rewrite H0.
            simplify.
            equality.
         ++ specialize e with A l.
            linear_arithmetic.
      -- simplify.
         rewrite nth_error_app1.
         ++ apply IHl. linear_arithmetic.
         ++ specialize e with A l.
            linear_arithmetic.
Qed.

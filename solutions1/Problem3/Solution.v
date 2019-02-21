Require Import Frap Modeling.

Require Import Problem.

Theorem useless_is_uselsss: forall (e: natExp) (v: valuation),
  eval_nat_exp e v = eval_nat_exp (uselessTransformation e) v.
Proof.
  simplify.
  induct e.
  + simplify; trivial.
  + simplify; trivial.
  + specialize IHe1 with v; specialize IHe2 with v; simplify; linear_arithmetic.
  + specialize IHe1 with v; specialize IHe2 with v; simplify; linear_arithmetic.
  + specialize IHe1 with v; specialize IHe2 with v; simplify; equality.
  + simplify.
    apply IHe.
Qed.

Ltac search e1 e2 IHe1 IHe2 :=
    simplify; cases e1; try (simplify; equality);
    cases e2; try (simplify; equality);
      rewrite IHe1;
      rewrite IHe2;
      simplify;
      equality.

Theorem constants_reducer_correct: forall (e: natExp) (v: valuation),
  eval_nat_exp e v = eval_nat_exp (constantsReducer e) v.
Proof.
  simplify.
  induct e; try (simplify; equality).
  + search e1 e2 IHe1 IHe2.
  + search e1 e2 IHe1 IHe2.
  + search e1 e2 IHe1 IHe2.
Qed.
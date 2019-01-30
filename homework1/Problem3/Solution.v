Require Import Frap Modeling.

Require Import Problem.

Theorem useless_is_uselsss: forall (e: natExp) (v: valuation),
  eval_nat_exp e v = eval_nat_exp (uselessTransformation e) v.
Proof.
Admitted.

Theorem constants_reducer_correct: forall (e: natExp) (v: valuation),
  eval_nat_exp e v = eval_nat_exp (constantsReducer e) v.
Proof.
Admitted.

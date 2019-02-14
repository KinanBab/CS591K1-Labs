Require Import Frap Imperative Hoare.

Definition swap_program : cmd :=
    ("tmp" <- "x";;
    "x" <- "y";;
    "y" <- "tmp")%cmd.

Definition max_program : cmd :=
    (_if_ "x" < "y" _then_
      "m" <- "y"
    _else_
      "m" <- "x"
    _done_)%cmd.

Definition fact_program (invariant: assertion) : cmd :=
  ("acc" <- 1;;
  {{ invariant }}
  _while_ 0 < "n" _loop_
    "acc" <- "acc" * "n";;
    "n" <- "n" - 1
  _done_)%cmd.

Fixpoint fact_specs (n: nat): nat :=
  match n with
  | 0 => 1
  | S n' => n * fact_specs n'
  end.





































































Lemma fact_base: forall (n: nat),
  n = 0 ->
  fact n = 1.
Proof.
  simplify; subst; simplify; trivial.
Qed.

Lemma fact_rec : forall n,
  n > 0
  -> fact n = n * fact (n - 1).
Proof.
  simplify; cases n; simplify; try linear_arithmetic.

  Check minus_n_O.

  pose minus_n_O.
  symmetry in e.
  rewrite e in *.
  linear_arithmetic.
Restart.
  Hint Rewrite <- minus_n_O.
  simplify; cases n; simplify; linear_arithmetic.
Qed.
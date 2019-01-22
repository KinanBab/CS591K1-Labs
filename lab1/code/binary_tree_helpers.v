Require Import Frap.
Require Import Nat Bool.

Ltac expand_ands :=
  (repeat match goal with
  | [ H: andb _ _ = true |- _] => symmetry in H
  | [ H: true = andb _ _ |- _] => apply andb_true_eq in H; invert H
  end);
  (repeat match goal with
  | [ H: true = _ |- _ ] => symmetry in H
  | [ H: false = _ |- _ ] => symmetry in H
  end).

Ltac expand_ands_no_symmetry :=
  (repeat match goal with
  | [ H: andb _ _ = true |- _] => symmetry in H
  | [ H: true = andb _ _ |- _] => apply andb_true_eq in H; invert H
  end).

Ltac comparison_bool_to_prop :=
  (repeat match goal with
  | [ H: Nat.eqb _ _ = true |- _ ] => apply Nat.eqb_eq in H
  | [ H: Nat.eqb _ _ = false |- _ ] => apply Nat.eqb_neq in H
  | [ H: Nat.leb _ _ = true |- _ ] => apply Nat.leb_le in H
  | [ H: Nat.leb _ _ = false |- _ ] => apply Nat.leb_nle in H
  | [ H: Nat.ltb _ _ = true |- _ ] => apply Nat.ltb_lt in H
  | [ H: Nat.ltb _ _ = false |- _ ] => apply Nat.ltb_nlt in H
  | [ |- Nat.eqb _ _ = true] => apply Nat.eqb_eq
  | [ |- Nat.eqb _ _ = false] => apply Nat.eqb_neq
  | [ |- Nat.leb _ _ = true] => apply Nat.leb_le
  | [ |- Nat.leb _ _ = false] => apply Nat.leb_nle
  | [ |- Nat.ltb _ _ = true] => apply Nat.ltb_lt
  | [ |- Nat.ltb _ _ = false] => apply Nat.ltb_nlt
  end).
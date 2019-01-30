Module Type Warmup.
  Axiom DeMorgan3: forall (p q: Prop),
    ~ (p \/ q) -> (~p /\ ~q).

  Axiom DeMorgan2: forall (p q: Prop),
    (~p \/ ~q) -> ~ (p /\ q).

  Axiom DeMorgan4: forall (p q: Prop),
    (~p /\ ~q) -> ~ (p \/ q).
End Warmup.
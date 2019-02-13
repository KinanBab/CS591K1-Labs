Require Import Frap Imperative.

(* Modeling Hoare logic rules and syntax 
 * Credits: Adam Chlipala - FRAP https://github.com/achlipala/frap
 *)


(* Hoare logic rules: ways to derive what is called a 'Hoare logic triple'
   A triple is a statement on the form {{ P }} <command> {{ Q }}, where P is a pre-condition assertion
   Q is a post-condition assertion, and <command> is some command/program.
   If we can derive the triple {{ P }} <command> {{ Q }} from our rules,
   then we have proven that if we start the program in a state satisfying P,
   then if we finish executing the progam, we will arrive at a state satisfying Q.
 *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P, hoare_triple P Skip P

| HtAssign : forall (P : assertion) x e,
  hoare_triple P (AssignVar x e) (fun h v => exists v', P h v' /\ v = v' $+ (x, eval e h v'))

| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (AssignMem e1 e2) (fun h v => exists h', P h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))

| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R

| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun h v => P h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun h v => P h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun h v => Q1 h v \/ Q2 h v)

| HtWhile : forall (I P : assertion) b c,
  (forall h v, P h v -> I h v)
  -> hoare_triple (fun h v => I h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun h v => I h v /\ beval b h v = false)

| HtAssert : forall P I : assertion,
  (forall h v, P h v -> I h v)
  -> hoare_triple P (Assert I) P

| HtConsequence : forall (P Q P' Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, P' h v -> P h v)
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P' c Q'.

(* Special case of consequence: keeping the precondition; only changing the
 * postcondition. No need to define this as a rule, since this directly follows
 * from the consequence rule. *)
Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

(* Easy-to-use notation for Hoare triples *)
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c%cmd Q) (at level 90, c at next level).


(* Helper tactic for traversing through a program and applying Hoare Logic rules *)
Ltac ht1 := apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq
            || eapply HtIf || eapply HtWhile || eapply HtAssert
            || eapply HtStrengthenPost.

Ltac t := cbv beta; propositional; subst;
          repeat match goal with
                 | [ H : ex _ |- _ ] => invert H; propositional; subst
                 end;
          simplify;
          repeat match goal with
                 | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
                 | [ H : ?E = ?E |- _ ] => clear H
                 end; simplify; propositional; auto; try equality; try linear_arithmetic.

Ltac ht := simplify; repeat ht1; t.

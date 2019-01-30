Require Import Frap.

(* Let us try to find AND introduction from class *)
Search (_ -> _ -> _ /\ _).
Check conj. (* This is the and introduction rule *)
Locate conj. (* This is where it is located, you can find its documenation here https://coq.inria.fr/library/Coq.Init.Logic.html *)
Check proj1. (* This is equivalent to (and elimination 1) *)
Check proj2. (* This is equivalent to (and elimination 2) *)

Search (_ -> _ -> _ \/ _). (* trying to find or introduction *)
Check or_introl. (* or-introduction-1 *)
Check or_intror. (* or-introduction-2 *)

(* Try to find -> Implication and -> elimination *)
(* Coq supports all the proof rules we saw in class (https://www.dropbox.com/s/s1on8nhksx4metg/lecture_slides_02.pdf?dl=0 slide 8)
   It also supports classical logic, but you will have to import it, since Coq uses intuitionistic logic by default *)


(* Here is a coq proof for de Morgan's law (3) from
   https://www.dropbox.com/s/li86bh9vgztvfzq/natural-deduction-examples-in-IPC.pdf?dl=0 page 5 *)
Theorem DeMorgan3: forall (p q: Prop),
  ~ (p \/ q) -> (~p /\ ~q).
Proof.
  intros. (* creates a box: by assuming the left hand side of the implication *)
  assert (p -> False). (* we want to use the fact that p -> False, but we have to prove it first *)
  + intros. (* prove p -> False, first create a box *)
    apply or_introl with (B := q) in H0. (* \/I in hypothesis H0 *)
    apply absurd with (A := (p \/ q)); assumption. (* false elimination and ~ introduction *)
  + (* notice H0 *)
    assert (q -> False).
    - intros.
      apply or_intror with (A := p) in H1.
      apply absurd with (A := (p \/ q)); assumption.
    - apply conj; assumption. (* Conjunction introduction *)

(* That is a bit tedious, here is an alternate way *)
Restart.
  (* In reality we would do this, but for this homework, this is not allowed *)
  propositional. (* Done! *)
Restart.
  tauto. (* Also Done! *)
Restart.
  first_order. (* Done as well *)
Qed.

(* HINT: you may want to duplicate a hypothesis (say it is called H) before you apply
   something like proj1 or proj2 in it, so that a copy of the hypothesis remains
   after application. you can do that using:
    assert (H' := H).
   where H' is the copy name, and H is the name of hypothesis to duplicate *)

(* Part 1 - Prove deMorgan Law 2
Page 4 in https://www.dropbox.com/s/li86bh9vgztvfzq/natural-deduction-examples-in-IPC.pdf?dl=0 *)
(* DO NOT USE PROPOSITIONAL, TAUTO, or FIRST_ORDER *)
Theorem DeMorgan2: forall (p q: Prop),
  (~p \/ ~q) -> ~ (p /\ q).
Proof.
Admitted.


(* Part 2 - Prove deMorgan Law 4: Remember you will need Classical logic's Law of Excluded middle for this *)
Require Import Classical. (* Imports the classical logic library with the classical logic axiom: law of excluded middle *)
Check NNPP. (* Law of excluded middle *)
(* Using NPP will allow you to carry on with the proof at step 9 in page 6 in 
https://www.dropbox.com/s/li86bh9vgztvfzq/natural-deduction-examples-in-IPC.pdf?dl=0 *)

(* DO NOT USE PROPOSITIONAL, TAUTO, or FIRST_ORDER *)
Theorem DeMorgan4: forall (p q: Prop),
  (~p /\ ~q) -> ~ (p \/ q).
Proof.
  (* Proof goes here *)

Admitted.

(* Answer to part 3 goes here, put it in a comment: *)
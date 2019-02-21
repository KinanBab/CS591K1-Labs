(* Hoare logic *)
Require Import Frap Modeling.

(* Hoare logic is often though of in terms of triplets *)
(* A Hoare triplet is made out of a pre-condition P, a statement from the program c, and a post-condition Q *)
(* A Hoare triplet P c Q means that if P is true on the state of the program (its variables and memory) entering
   into c, then Q will be true on the state of the program after executing c *)

(* Hoare logic allows us to move through an iterative program, and carry an assertion through.
   The assertion is modified according to every statement of the program.
   If we can show that starting from an assertion a1, we traverse the program and reach assertion a2
   then we proved that for every input on which a1 holds, the ouput must satisfy a2.
   a1 and a2 are sometimes called pre-condition and post-condition. *)
(* Hoare logic allows us to traverse the program staticially/symbolically: we do not really execute the program
   in the full sense of the word:
   1. We do not iterate over loops the way we would if we are executing the program. Instead, we reason about the loop
      in a single short using what is called a 'loop invariant'.
   2. We do not need concrete inputs to traverse the program: all we need some precondition on the input, for most generality
      the pre condition can be 'true', which means we are making no assumptions about the inputs. *)
(* The rules below are syntax-driven, you have a rule per statement in our language, so that we can move through the program
   effecetively. Note that these rules do not have to be taken for grantneed, they can be proven to be sound (i.e. correct)
   relative to the semantics. *)
Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
(* Skip does not change the assertion *)
| HtSkip : forall P, hoare_triple P Skip P

(* Variable assignment, arguebly this is the most un-natural looking rule here
   The problem is that the assertion may be referring to the variable that just got overwritten.
   Our new assertion is then that both:
    1. Some valuation exists that satisfy our OLD assertion,
and 2. This valuation only differs from the NEW valuation after executing assignment
       in the value of the varaible being assigned. *)
| HtAssign : forall (P : assertion) x e,
  hoare_triple P (AssignVar x e) (fun h v => exists v', P h v' /\ v = v' $+ (x, eval e h v'))

(* Similar to above but for heap *)
| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (AssignMem e1 e2) (fun h v => exists h', P h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))

(* Sequencing: if P c1 gets us to Q, and Q c2 gets us to R, then P (c1; c2) gets us to R *)
| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R

(* If: The post condition is either that of the true branch or the false branch *)
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun h v => P h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun h v => P h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun h v => Q1 h v \/ Q2 h v)

(* While: we do not need to consider the case where the while condition is false, 
   since that is equivalent to Skip by our semantics. *)
(* If the condition is true, and the invariant holds before entering the loop, than after finishing
   the loop completely, the condition must become false, and the invariant must still hold *)
(* The condition becomes false, cause otherwise, the loop is not completed yet. The invariant
   must hold by definition of invariant *)
| HtWhile : forall (I P : assertion) b c,
  (forall h v, P h v -> I h v)
  -> hoare_triple (fun h v => I h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun h v => I h v /\ beval b h v = false)

(* An assertion is only accepted if the pre-condition implies it, in other words,
   if the assertion can be shown to be true at the point in the program *)
| HtAssert : forall P I : assertion,
  (forall h v, P h v -> I h v)
  -> hoare_triple P (Assert I) P

(* Finally: this can be used for flexibility, you can strengthen the pre-condition
   or weaken the post-condition arbitrarily, this is usually called *the consequence rule* *)
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


Notation "{{ P }} c {{ Q }}" := (hoare_triple P c%cmd Q) (at level 90, c at next level).
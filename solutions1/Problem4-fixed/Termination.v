Require Import Frap Modeling Hoare Helpers Problem Solution.

(* Hoare logic only gives us partial correctness, it can be extended to gives us total correctness (i.e. termination)
   by using a loop variant that is always decreasing betwen consecutive iterations. *)

(* READ MORE HERE https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/Oct17.pdf *)

Inductive simple_termination : cmd -> Prop :=
| TrSkip : simple_termination Skip

| TrAssign : forall x e,
  simple_termination (AssignVar x e)

| TrWrite : forall (e1 e2 : exp),
  simple_termination (AssignMem e1 e2)

| TrSeq : forall c1 c2,
  simple_termination c1
  -> simple_termination c2
  -> simple_termination (Seq c1 c2)

| TrIf : forall b c1 c2,
  simple_termination c1
  -> simple_termination c2
  -> simple_termination (If_ b c1 c2)

(* Encoding of rule in slide 8 (page 142) from https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/Oct17.pdf *)
(* Note1: we are using a simpler (sound but even less complete) version of termination rules here, since we
     do not include any pre or post condition, to simplifiy our analysis.
     This is why we do not include [P] in our analysis.
   Note2: our variant is a natural, which means it is also >= 0, we do not need to prove that,
     variants that try to cheat by decreasing infinitly (to -infinity) are impossible, since 0 - anything = 0
     when dealing with natural types in Coq. *)
| TrWhile : forall I b c,
  simple_termination c
  -> (exists E: heap -> valuation -> nat,
        forall (n: nat),
          {{fun h v => beval b h v = true /\ (E h v) = n }}
          c
          {{fun h v => (E h v) < n }}
     )
  -> simple_termination (While_ I b c)

| TrAssert : forall I, simple_termination (Assert I).


(* We keep hoare logic rules and termination rules seperate, so that we can use the theorem from
   the solutions in our proof, without proving it again.
   The slides at https://www.cl.cam.ac.uk/archive/mjcg/HoareLogic/Lectures/Oct17.pdf
   combine them together to form a new set of rules that give total correctness.
   In most cases, the modeling here will not be enough to prove total correctness (it is still sound though),
   since provers need to use assertions and invariants and other information about the program state, from
   the hoare logic rules, to be able to prove termination. *)
Definition total_correctness (P Q: assertion) (c: cmd): Prop :=
  simple_termination c /\ ({{P}} c {{Q}}).

Notation "[[ P ]] c [[ Q ]]" := (total_correctness P Q c%cmd ) (at level 90, c at next level).

(* Helpful automated tactics (similar to Hoare Logic tactics *)
Ltac tr1 := apply TrSkip || apply TrAssign || apply TrWrite || eapply TrSeq
            || eapply TrIf || eapply TrWhile || eapply TrAssert.

Ltac tr := simplify; repeat tr1.

Theorem merge_totally_correct: forall (len1 len2: nat),
  [[ fun h v => is_sorted h 0 len1 /\ is_sorted h len1 (len1 + len2) ]]
    merge_program len1 len2 merge_invariant
  [[ fun h v => (is_sorted h (len1 + len2) (len1 + len2 + len1 + len2)) ]].
Proof.
  unfold total_correctness; simplify; propositional.
  + tr.
    (* Must choose the variant *)
    exists (fun h v => (len1 + len2 + len1 + len2) - (v $! "i")).
    ht.
  + apply merge_correct.
Qed.



Require Import Frap Modeling Hoare Helpers.

Require Import Problem.

(* Look at Problem.v to see what these things mean *)

(* Start with the simple lemma *)
Lemma is_sorted_smaller: forall (arr: heap) (startI endI endI': nat),
  is_sorted arr startI endI -> endI' <= endI -> is_sorted arr startI endI'.
Proof.
  simplify.
  unfold is_sorted in *.
  first_order.
  specialize H with i1 i2.
  linear_arithmetic.
Qed.

(* Define the loop invariant *)
Definition merge_invariant (len1 len2: nat): assertion :=
  fun h v => is_sorted h (len1 + len2) (v $! "i").

(* Prove the basic version of correctness *)
Theorem merge_correct: forall (len1 len2: nat),
  {{ fun h v => is_sorted h 0 len1 /\ is_sorted h len1 (len1 + len2) }}
  merge_program len1 len2 merge_invariant
  {{ fun h v => (is_sorted h (len1 + len2) (len1 + len2 + len1 + len2)) }}.
Proof.
  unfold merge_invariant in *;
  (* A somewhat manual solution: go through the statements one at a time
     each time manually choose and apply the appropriate hoare logic rule *)
  simplify.
  eapply HtSeq.
  eapply HtAssign.
  eapply HtSeq.
  eapply HtAssign.
  eapply HtSeq.
  eapply HtAssign.
  eapply HtStrengthenPost.
  + eapply HtWhile.
    * t.
      unfold is_sorted.
      simplify.
      propositional. linear_arithmetic.
    * ht.
      - unfold is_sorted in *.
        simplify. first_order.
      - unfold is_sorted in *.
        simplify. first_order.
      - unfold is_sorted in *.
        simplify. first_order.
      - unfold is_sorted in *.
        simplify. first_order.
  + t.
    apply is_sorted_smaller with (endI := (v $! "i")); assumption.

  (* Alternative more automated way of proving the same thing *)
  Restart. (* Restarts the proof *)
  unfold merge_invariant.
  ht; try (unfold is_sorted in *; simplify; first_order).
  + unfold is_sorted. propositional. simplify. linear_arithmetic.
  + specialize H0 with i1 i2.
    propositional.
    linear_arithmetic.
Qed.

(* Put any bonus parts code here *)


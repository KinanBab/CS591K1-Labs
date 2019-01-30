Require Import Frap Modeling Hoare Helpers.

Require Import Problem.

(* Look at Problem.v to see what these things mean *)

(* Start with the simple lemma *)
Lemma is_sorted_smaller: forall (arr: heap) (startI endI endI': nat),
  is_sorted arr startI endI -> endI' <= endI -> is_sorted arr startI endI'.
Proof.
Admitted.

(* Define the loop invariant *)
Definition merge_invariant (len1 len2: nat): assertion :=
  fun (h: heap) (v: valuation) => False.

(* Prove the basic version of correctness *)
Theorem merge_correct: forall (len1 len2: nat),
  {{ fun h v => is_sorted h 0 len1 /\ is_sorted h len1 len2 }}
  merge_program len1 len2 merge_invariant
  {{ fun h v => (is_sorted h (len1 + len2) (len1 + len2 + len1 + len2)) }}.
Proof.
  unfold merge_invariant in *.
  (* Look at the hints in Helpers.v and Problem.v *)
Admitted.

(* Put any bonus parts code here *)


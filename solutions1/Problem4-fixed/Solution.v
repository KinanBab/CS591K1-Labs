Require Import Frap Modeling Hoare Helpers.

Require Import Problem.

(* Look at Problem.v to see what these things mean *)

(* Helpful lemma proofs *)
Lemma is_sorted_smaller: forall (arr: heap) (startI endI endI': nat),
  is_sorted arr startI endI -> endI' <= endI -> is_sorted arr startI endI'.
Proof.
  unfold is_sorted; t.
  apply H; linear_arithmetic.
Qed.
Lemma singletone_is_sorted: forall (arr: heap) (startI: nat),
  is_sorted arr startI (startI + 1).
Proof.
  unfold is_sorted; t.
Qed.
Lemma is_sorted_extend: forall (arr: heap) (startI endI x: nat),
  is_sorted arr startI endI
  -> arr $! (endI - 1) <= x
  -> is_sorted (arr $+ (endI, x)) startI (endI + 1).
Proof.
  unfold is_sorted; t.
  cases (k2 <? endI); comparison_bool_to_prop; simplify; first_order.
  cases (k1 <? endI - 1); comparison_bool_to_prop.
  ++ assert (arr $! k1 <= arr $! (endI - 1)) by (apply H; propositional; linear_arithmetic).
     linear_arithmetic.
  ++ assert (k1 = endI - 1) by linear_arithmetic.
     rewrite H3 in *.
     assumption.
Qed.
Lemma is_sorted_remains_sorted_with_useless: forall (arr: heap) (startI endI: nat) (i x: nat),
  is_sorted arr startI endI
  -> i >= endI
  -> is_sorted (arr $+ (i, x)) startI endI.
Proof.
  unfold is_sorted; t.
Qed.

(* Define the loop invariant *)
Definition merge_invariant (len1 len2: nat): assertion :=
  fun h v =>
    (* A: we increasingly make the final array sorted as "i" increases*)
    is_sorted h (len1 + len2) (v $! "i")
    (* B: the input arrays are unchanged and remain sorted *)
    /\ is_sorted h 0 len1 /\ is_sorted h len1 (len1 + len2)
    (* lower bounds on the counters *)
    /\ (v $! "i") >= len1 + len2 /\ (v $! "i2" >= len1) /\ (v $! "i" >= (v $! "i1") + (v $! "i2") + len2)
    (* C: Very important strengthening of the invaraint:
       The bottom two terms are very similar, but not very intuitive, they are needed because they
       combine values from the current iteraion ("i", "i1", "i2"), with values from the previous iteration ("i"-1).
       These do not always apply, they only apply when "i"-1 is within range, and "i1", "i2" did not finish looping over
       their respective arrays *)
    /\ ((v $! "i" > len1 + len2) -> (v $! "i1" < len1) -> h $! (v $! "i" - 1) <= h $! (v $! "i1"))
    /\ ((v $! "i" > len1 + len2) -> (v $! "i2" < len1 + len2) -> h $! (v $! "i" - 1) <= h $! (v $! "i2"))
    (* upper bounds on the counters *)
    /\ (v $! "i1" <= len1) /\ (v $! "i2" <= len1 + len2)
    (* Z: Either: "i1" is not done yet, "i2" is not done yet, the input arrays are empty, or the loop/program is done *)
    /\ (v $! "i1" < len1 \/ v $! "i2" < len1 + len2 \/ (len1 = 0 /\ len2 = 0) \/ v $! "i" = len1 + len2 + len1 + len2).

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
    * unfold is_sorted. t.
    * eapply HtSeq.
      ++ ht.
      ++ t.
         eapply HtStrengthenPost.
         -- apply HtAssign.
         -- t. (* TAKES A LONG TIME  *)
            (* we get many goals (24) but they only have 3 distinct types, we only really need 3 proofs 
               that we re-use (in this case copy-paste) to prove all goals of the same type. *)
            (* t already proved most of the goals (there is something near 100 of them) 
               for us, and left only the things it got stuck on, if you look at t's defintion
               you will see it cannot do either case analysis (it is very hard to automatically know what to case analyse)
               or apply external lemmas. So t gets stuck on proofs that require using these features. *)
            (* The reason we have so many goals is that we have to prove that the invariant remains true after an iteration, notice
               that the invariant is made out 11 conditions combined together with ands, we need to prove every single one of the conditions.
               to top it off, the program has 3 nested if-else conditions, each combiniation produces different state (post-condition) and thus, we end
               up having to prove the same condition from the invariant from every one of them, additionally sequencing and assignments inside the loop
               body produce additional goals. t solves most of the obvious ones automatically, but gets stuck on things that depend on some conditions that
               we need to run cases on *)

            (* Type one, corresponds to A in the invariant: the first type is goals that prove that the newly extended output array is sorted *)
            (* all of these goals are very similar and have the same proof:
               1. We have two cases: either this is the first iteration, or this is some later iteration.
               2. if this is some later iteration, we can use is_sorted_extend to extend the already sorted array by one element!
               3. if this is the first iteration, that means the output array currently only has one element, and is trivially sorted *)
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.
            ** cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop.
               +++ assert (x0 $! "i" > len1 + len2) by linear_arithmetic.
                   propositional.
                   apply is_sorted_extend; assumption.
               +++ assert (x0 $! "i" = len1 + len2) by linear_arithmetic.
                   rewrite H1 in *. 
                   apply singletone_is_sorted.

            (* Type two: goals corresponding with sortedness of input arrays, condition B in the invaraint *)
            (* we get six goals per input array, all can be solved by noticing that the input arrays are unchanged *)
            (* Notice that the proof of [is_sorted_remains_sorted_with_useless] is just [unfold is_sorted; t].
               so we could have proved these goals with just that. We use the lemma for clarity/modularity *)
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.
            ** apply is_sorted_remains_sorted_with_useless; try assumption; linear_arithmetic.

            (* Type four: almost trivial residual goals from condition C in the invariant.
               t is stuck here because it does not know how to [apply] is_sorted *)
            ** apply H2; propositional; linear_arithmetic.
            ** apply H2; propositional; linear_arithmetic.
            ** apply H2; propositional; linear_arithmetic.
            ** apply H8; propositional; linear_arithmetic.
            ** apply H8; propositional; linear_arithmetic.
            ** apply H6; propositional; linear_arithmetic.

  (* We are done with the loop, now we want to prove that the invariant after the loop
     terminates imply the final post-condition. *)
  + ht.
    (* three cases each corresponding to one of the options in Z, the case related to the third
       option is trivial and is proven automatically by ht for us. *)
    - eapply is_sorted_smaller.
      * exact H.
      * linear_arithmetic.
    - eapply is_sorted_smaller.
      * exact H.
      * linear_arithmetic.
    - eapply is_sorted_smaller.
      * exact H.
      * linear_arithmetic.

Restart.
  (* A slightly more automated verison of the proof *)
  unfold merge_invariant.

  (* We chain all these proofs to avoid copy-pasting *)
  (* will traverse all of the program and give us all the required sub goals: uses t internally *)
  ht;
  (* t does not know to unfold is_sorted, we will try to help it by unfolding is_sorted for it *)
  (* the complicated try; fail pattern is because I do not want to unfold is_sorted for goals that still need
  proving, since that will make them look more complicated on the screen *)
  try (unfold is_sorted; t; fail);

  (* The proof for type A: but written as a chain *)
  try (
    cases (len1 + len2 <? (x0 $! "i")); comparison_bool_to_prop;
      (assert (x0 $! "i" > len1 + len2) by linear_arithmetic;
      propositional;
      apply is_sorted_extend; assumption)
    ||
      (assert (x0 $! "i" = len1 + len2) by linear_arithmetic;
      rewrite H1 in *;
      apply singletone_is_sorted)
  );

  (* Proof for type C as a chain *)
  (* this is a more brute-force style of automation, we could have been smarter and pattern
     matched on the goal to see which of the assumptions we should apply. *)
  try (apply H2; propositional; linear_arithmetic);
  try (apply H8; propositional; linear_arithmetic);
  try (apply H6; propositional; linear_arithmetic);

  (* Proof for the three cases after the while loop: the invariant imply the final post-condition *)
  eapply is_sorted_smaller; try exact H; linear_arithmetic.
Qed.

(* Put any bonus parts code here *)


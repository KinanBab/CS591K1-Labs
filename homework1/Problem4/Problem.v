Require Import Frap Modeling Hoare Helpers.

(* This logical formula is a proposition that described what it means
   for an array to be sorted. The array in question here is
   stored in the given heap, between indices [startI, endI) *)
Definition is_sorted (arr: heap) (startI: nat) (endI: nat): Prop :=
  forall (i1 i2: nat), (lt startI i1) /\ (lt i1 i2) /\ (lt i2 endI) -> (le (arr $! i1) (arr $! i2)).

(* The program for merging two arrays:
   1. It assumes that two arrays are already provided on the heap, the 
   first between indices [0, len1) and the second between [len1, len1 + len2).
   2. It writes out a merged sorted array to the end of the heap, so
   that the first two arrays are not changed, and are followed by the sorted
   array between indices [len1+len2, 2*(len1+len2) )
   3. The assertion for the for loop is given as a parameter, to allow you
   to define it without having to modify this program. The parameters to the
   assertion will be len1 and len2. *)
Definition merge_program (len1 len2: nat) (I: nat -> nat -> assertion): cmd := (
  (* i will be the current index in the merged resulting array *)
  "i" <- (len1 + len2) ;;
  "i1" <- 0 ;; (* current index in first array *)
  "i2" <- len1 ;; (* current index in the second array *)

  {{ I len1 len2 }} (* you will define this invariant *)
  _while_ "i" < (len1 + len2 + len1 + len2) _loop_
    (* standard merge: if arr1[i1] < arr2[i2], we add arr[i1] to the 
        end of the merged array and increment i1, if arr1[i1] >= arr[i2],
        we choose arr[i2]. We must pay attention to special cases where
        i1 or i2 are out of range. *)
    _if_ "i1" < len1 _then_
      _if_ "i2" < len1 + len2 _then_
        _if_ *["i1"] < *["i2"] _then_
          *["i"] <- *["i1"] ;;
          "i1" <- "i1" + 1
        _else_
          *["i"] <- *["i1"] ;;
          "i1" <- "i1" + 1
        _done_
      _else_
        *["i"] <- *["i1"] ;;
        "i1" <- "i1" + 1
      _done_
    _else_
      (* i2 must be < len2 *)
      *["i"] <- *["i2"] ;;
      "i2" <- "i2" + 1
    _done_
  _done_) % cmd.

Module Type Problem4.
  (* Start off by proving this simple lemma:
     if the array starting at startI and ending at endI is sorted,
     then the sub array starting at startI and ending at endI' is also sorted,
     where endI' <= endI. *)
  Axiom is_sorted_smaller: forall (arr: heap) (startI endI endI': nat),
    is_sorted arr startI endI -> endI' <= endI -> is_sorted arr startI endI'.

  (* You must define the invariant for the while loop of the program above:
     Remember, the invariant must:
     1. Be true before the execution of the while loop start.
     2. Remain true after each execution of the while loop.
     3. Imply the post condition we desired (defined below) *)
  Parameter merge_invariant: nat -> nat -> assertion.

  (* The first version of correctness: the resulting array must be sorted,
     given that the two input arrays are sorted *)
  (* Helpers.v contain some helpful tactics that will automate a large chunk of
     this proof, as well as some hints, read the comments there carefully *)
  (* HINT: At some point in the proof, you will reach the body of the while loop,
     using [ht1] or [ht] or manually applying the HtIf rule will spit out
     4 goals for you, this is because we have 4 cases in the body of the loop:
     1. i1 is out of range
     2. i2 is out of range
     3. both in range but the element at i1 < element at i2.
     4. both in range but the element at i1 >= element at i2.
     The goals produces at all these cases are very similar, and can be
     solved by exactly the same proof if written generally enough. Consider
     using the tactic [first_order] in these proofs! *)
  (* HINT: In both the manual and automatic version of my solutions, I got a total
     of 6 proof obligations.
     1. for showing the invariant of the while loop is initally true.
     2-5. the proof obligations corresponding to the cases above.
     6. Obligation for showing that the loop invariant implies the post condition
        when the loop is done. You will want to use 'is_sorted_smaller' here. *)
  Axiom merge_correct: forall (len1 len2: nat),
    {{ fun h v => is_sorted h 0 len1 /\ is_sorted h len1 len2 }}
    merge_program len1 len2 merge_invariant
    {{ fun h v => (is_sorted h (len1 + len2) (len1 + len2 + len1 + len2)) }}.
End Problem4.


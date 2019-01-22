Require Import Frap.

(* Let us define a binary tree (of natural numbers) *)
Inductive tree :=
| nil
| cons (left: tree) (root: nat) (right: tree).

(*       1       *)
(*   2      4    *)
(*     3         *)
Definition example := 
  cons (cons nil 2 (cons nil 3 nil)) 1 (cons nil 4 nil).

(* To define search, we need to check for equality and less than for nats,
   as well as boolean ands and ors *)
Search (nat -> nat -> bool).
Print Nat.eqb.
Print Nat.leb.
Search (bool -> bool -> bool).
Print orb.

Fixpoint search (t: tree) (n: nat) : bool :=
  match t with
  | nil => false
  | cons l e r =>
      let r1 := (Nat.eqb e n) in
      let r2 := (search l n) in
      let r3 := (search r n) in
        orb r1 (orb r2 r3)
  end.

Compute (search example 2).
Compute (search example 3).

Fixpoint binary_search (t: tree) (n: nat) : bool :=
  match t with
  | nil => false
  | cons l e r =>
      if (Nat.eqb e n) then true
      else if (Nat.leb e n) then binary_search r n
      else binary_search l n
  end.

(* It does not always work! cause it requires the tree to be a search tree (sorted)! *)
Compute (binary_search example 1).
Compute (binary_search example 2).
Compute (binary_search example 3).
Compute (binary_search example 4).


(* MODELING *)
(* How do we define that a tree is a search tree ? *)
(* One way: define a function that takes a tree as a parameter, and checks if it is search tree *)

Fixpoint all_less (t: tree) (n: nat) : bool :=
  match t with
  | nil => true
  | cons l e r =>
      let r1 := (Nat.leb e n) in
      let r2 := (all_less l n) in
      let r3 := (all_less r n) in
        andb r1 (andb r2 r3)
  end.

Fixpoint all_greater (t: tree) (n: nat) : bool :=
  match t with
  | nil => true
  | cons l e r =>
      let r1 := (Nat.leb n e) in
      let r2 := (all_greater l n) in
      let r3 := (all_greater r n) in
        andb r1 (andb r2 r3)
  end.

Fixpoint is_binary_search (t: tree) : bool :=
  match t with
  | nil => true
  | cons l e r =>
    let r1 := is_binary_search l in
    let r2 := is_binary_search r in
    let r3 := (all_less l e) in
    let r4 := (all_greater r e) in
      andb r1 (andb r2 (andb r3 r4))
  end.
(* Note: this is not the best implementation for checking if a tree is a search tree
 * The runtime is terrible, a leaf node is visited as many times as it has parents!
 * More efficient implementations exist, but we do not care, in fact, it is better
 * for us to use an inefficient but easy-to-write-corretly version, since we will
 * use this function only statically (at compile time) for proofs as you will see.
 * Note that this is part of our modeling, if we made a mistake expressing what a search tree
 * is, the correctness of binary search will mean something different. *)


(* Proofs *)

(* We want to prove that binary search is correct, this could be formulated in many ways,
 * one easy such formulation is to prove that it produces the same output as regular linear search
 * on all SEARCH (sorted) trees.
 *)

(* Turns out we need these two small lemmas to help us in our correctness proofs
 * The main intuition in binary search, is that the element cannot exist in the subtree
 * that was eliminated / discarded, due to the sortedness of the tree, and the fact that
 * the element was greater/less than the root.
 *)

(* Syntax forall (param1: type) (param2: type), <formula>
 * expresses a statement that is true for all combinations of values for parameters of the given types
 * Important remark: boolean and prop types are different but very similar.
 *                   boolean is a computational type, that you can use or construct using functional code
 *                   prop (short for propositions) is a static concept used in proofs.
 *                   This distinction has important reasons that will become apparant later in the course.
 *                   true/false are booleans, True/False are props,
 *                   search t n has type boolean,
 *                   (search t n = false) has type prop,
 *                   (search t n = false) = False has type prop,
 *                   (search t n =? false) has type boolean.
 *
 * Syntax /\ is static and for Propositions, as opposed to andb/&& which is for booleans.
 * Syntax -> is implication for Propositions.
 * =, >, < gives back props (statements for proofs), =?, >?, <? give back booleans (values for code).
 * Coq gives us a bunch of helpers for translating booleans to props.
 *)
Require Import Bool.
Require Import binary_tree_helpers.

Lemma not_in_less:
  forall (t: tree) (e n: nat),
    (all_less t e = true) /\ n > e -> search t n = false.
Proof.
  simplify.
  propositional.
  induct t.
  + simplify. trivial.
  + simplify.

    expand_ands.
    specialize IHt1 with (n := n).
    specialize IHt2 with (n := n).

    apply IHt1 in H0; try assumption.
    apply IHt2 in H3; try assumption.
    clear IHt1 IHt2.

    apply orb_false_iff.
    propositional.
    - comparison_bool_to_prop.
      linear_arithmetic.
    - apply orb_false_iff; propositional; assumption.
Qed.

Lemma not_in_greater:
  forall (t: tree) (e n: nat),
    (all_greater t e = true) /\ n < e -> search t n = false.
Proof.
  simplify.
  propositional.
  induct t.
  + simplify. trivial.
  + simplify.

    expand_ands.
    specialize IHt1 with (n := n).
    specialize IHt2 with (n := n).

    apply IHt1 in H0; try assumption.
    apply IHt2 in H3; try assumption.
    clear IHt1 IHt2.

    apply orb_false_iff.
    propositional.
    - comparison_bool_to_prop.
      linear_arithmetic.
    - apply orb_false_iff; propositional; assumption.
Qed.

(* Main correctness theorem:
 * For every tree and number, if the tree is a search tree, then binary search 
 * gives the same result as linear search.
 *)
Theorem binary_search_correct:
 forall (t: tree) (n: nat), (is_binary_search t) = true ->
    (binary_search t n) = (search t n).
Proof.
  simplify.
  induct t.
  + unfold binary_search; unfold search.
    trivial.
  + simplify.
    cases (root =? n).
    - trivial.
    - cases (Nat.leb root n).
      * simplify.
        expand_ands.
        assert (search t1 n = false).
        ++ apply not_in_less with (e := root).
           propositional.
           comparison_bool_to_prop.
           linear_arithmetic.
        ++ rewrite H2.
           specialize IHt2 with n.
           apply IHt2 in H.
           rewrite H.
           propositional.
      * simplify.
        expand_ands.
        assert (search t2 n = false).
        ++ apply not_in_greater with (e := root).
           propositional.
           comparison_bool_to_prop.
           linear_arithmetic.
        ++ rewrite H2.
           specialize IHt1 with n.
           apply IHt1 in H0.
           rewrite H0.
           propositional.
           symmetry.
           apply orb_false_r.
Qed.
(*
 * Introduction to functional programming in Coq.
 * Functional programming?
 * 1. No mutuable variables / pointers in the usual imperative sense
 *    Variables are just names you assign to things.
 * 2. Less emphasis on loops and if-else conditions, more emphasis
 *    on recursion and *Pattern Matching*
 * 3. Inductive types are very common in functional programming.
 *    You can easily operate on them using recursion and pattern matching.
 *)

(* Require Import List. *)

(*
 * Keyword Inductive: Inductive type definition.
 * It is inductive because it is built bottom-up.
 *
 * Syntax := is assignment (similar to = in imperative languages)
 * Syntax |  for specifying cases of the definition (more specifically type constructors)
 *)
Inductive my_natural_linked_list : Type :=
  (* First case: Empty linked list contains no nodes *)
  (* Empty is the name of the constructor that gives us an Empty list *)
  (* Syntax : specifies the type of what is on the left hand side *)
  (* Notice that the type of Empty is my_natural_linked_list *)
  | Empty
  (* Second case: Non-empty linked list contains at least one node *)
  (* The one node is followed by a list which can be empty or not *)
  (* Syntax (name: type) specifies a parameter of a given type *)
  | Node (node: nat) (remaining: my_natural_linked_list).

(* Some examples, Look at the messages panel at the bottom right corner --> *)
Check Empty.
Check (Node 0 Empty).
Check Node 1 (Node 0 Empty).
Check my_natural_linked_list.

(* OK, but do we need to do that for every type?
 * What if I want a list of strings, or floats, or a list of lists ?
 * Must use polymorphism, define list for any element type
 * This is very similar to generics in Java or templates in C++
 * All are ways to acheive polymorphism *)

(*
 * Syntax (A: Type) specifies a *polymorphic* type parameter, similar to saying LinkedList<T> in Java.
 * Coq does not distinguish much between type parameters and *data* parameters, they are all parameters.
 * In a sense, the definition is defined w.r.t ALL possible types A, when you use the definition
 * you *specialize* it to a specific type.
 *)
Inductive my_linked_list (A: Type) :=
  | EmptyA (* this is commonly referred to as nil, the functional equivalent of null *)
  (* Notice this is the same as before, but now we use A as opposed to nat *)
  | NodeA (node: A) (remaining: my_linked_list A). (* commonly called cons, with parameters head and tail *)

Check EmptyA. (* Notice the forall statement --> *)
Check NodeA nat 3 (EmptyA nat). (* The types must be the same for an EmptyA and NodeA to compose *)
(* try to remove one of the nat type parameters in the line above
   it wont work anymore! *)

(* Annoying that we have to specify the type every time *)
(* But we can ask Coq to infer the types automatically ! *)
Set Implicit Arguments. (* Ask coq to infer implicity type arguments by default *)
Inductive my_list (A: Type) := (* must redefine list for implicit arguments to take effect *)
  | my_nil
  | my_cons (head: A) (tail: my_list A).
Arguments my_nil [A]. (* Ask coq to infer my_nil type from context *)

(* Much better now *)
Check my_nil.
Check my_cons 3 my_nil.
Check my_cons 3 (my_cons 2 my_nil).

(*
 * Ok, enough definitions, how do we use these types ?
 * With recursion !
 * Keyword Fixpoint: a recursive function definition
 *)
Fixpoint my_list_size (A: Type) (list: my_list A) : nat :=
  match list with
  | my_nil => 0
  | my_cons element list' => 1 + (my_list_size list')
  end.

(* Command Compute: ask coq to compute and print the statement *)
Compute my_list_size (my_cons 3 (my_cons 2 (my_cons 1 my_nil))).

Fixpoint last_element (list: my_list nat) : nat  :=
  match list with
  (* this could be confusing! ideally, we want some special null value,
      or an error, or to require that list is not empty *)
  | my_nil => 0
  (* this is all fine *)
  | my_cons head my_nil => head
  | my_cons head tail => last_element tail
  end.

Fixpoint reverse' (A: Type) (list accumulator: my_list A) : my_list A :=
  match list with
  | my_nil => accumulator
  | my_cons head tail =>
    reverse' tail (my_cons head accumulator)
  end.
Fixpoint reverse (A: Type) (list: my_list A) : my_list A :=
  reverse' list my_nil.

Compute reverse (my_cons 3 (my_cons 2 (my_cons 1 my_nil))).

Fixpoint my_list_sum (list: my_list nat) : nat :=
  match list with
  | my_nil => 0
  | my_cons element list' => element + (my_list_sum list')
  end.

Compute (my_list_sum (my_cons 3 (my_cons 2 (my_cons 1 my_nil)))). (* Gives 6 *)

(* Luckily we do not have to define all these things every
   time our selves *)
(* Coq has a large library of theories and data types for us to use *)
Require Import List.

Print list. (* Shows you the entire implementation *)
Check length. (* Shows you just the header *)
Search (list _ -> list _ -> list _). (* Search for anything with the given type expression in its header *)
Locate app. (* Finds the location/module of the thing you are looking for *)

(* Additionally, we are using Adam Chlipala's very nice library
   that simplifies Coq development and proofs a lot! *)
Require Import Frap.

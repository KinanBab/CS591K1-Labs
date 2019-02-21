Require Import Frap.

(*
 *
 * Modeling a full-feature Imperative programming language to allow us to reason about imperative programs in Coq 
 *
 *)


(* 
 * 1: Our imperative language constructs and syntax.
 *)

(* natural number expression *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| ReadMem (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Times (e1 e2 : exp)
| DivBy2 (e1: exp).

(* Those were the expressions of numeric type.  Here are the Boolean
 * expressions. *)
Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

(* Heap allows for pointer/index based access *)
Definition heap := fmap nat nat.
(* Values of variables (almost like the stack) *)
Definition valuation := fmap var nat.
(* An assertion allows us to check the state of the program
   on the heap and valuation, and see if it conforms with 
   some desired property *)
Definition assertion := heap -> valuation -> Prop.

(* The statements in our language, these do not have a value themselves
   but can have side effects (can make changes to the heap or valuation) *)
Inductive cmd :=
| Skip
| AssignVar (x : var) (e : exp)
| AssignMem (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)
(* Think of this more as an annotation
   something we will add to our programs that help us analyze them. *)
| Assert (a : assertion).

(* BEGIN syntax macros that won't be explained *)
(* These allow us to override Coq's syntax with our own *)
Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (ReadMem e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Times : cmd_scope.
Notation "e / '2'" := (DivBy2 e) (at level 70) : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | ReadMem dst' => AssignMem dst' src
  | Var dst' => AssignVar dst' src
  | _ => AssignVar "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'_if_' b '_then_' then_ '_else_' else_ '_done_'" := (If_ b then_ else_) (at level 75, b at level 0).
Notation "{{ I }} '_while_' b '_loop_' body '_done_'" := (While_ I b body) (at level 75).
Notation "'assert' {{ I }}" := (Assert I) (at level 75).
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.

(* Finite map notation: *)
(* <map> $? <key> -> Some <value> or None if key is not in the map *)
(* <map> $! <key> -> <value> or 0 if key is not in the map *)
(* <map> $+ (<key>, <value>) adds (key, value) to the map *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
(* END macros *)

(*
 * End of 1
 *)



(*
 * 2: The semantics of our programming languages: we are explaining
 *    to coq what each construct in our programming language mean
 *)

(* Interpreters for nat and bool expression *)
Fixpoint eval_div2 (n: nat): nat :=
  match n with
  | 0 => 0
  | S n =>
    match n with
    | 0 => 0 (* 1 / 2 = 0 *)
    | S n => 1 + eval_div2 n
    end
  end.

Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | ReadMem e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Times e1 e2 => eval e1 h v * eval e2 h v
  | DivBy2 e => eval_div2 (eval e h v)
  end.
Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
end.

(* This is different than the previous problems
   We will go through something like this in lab 3. *)
(* This is one way of encoding what is called small step semantics. 
   Instead of using an interpreter, which has several drawbacks, including problematic
   requirements on termination, we can use an inductive relation, to specify the meaning of the program
   one statement at a time (hence small-step). *)
(* This is an inductive relation of type (heap * valuation * cmd) -> (heap * valuation * cmd)
   in other words, it *relates* two tuples together, each made out of a heap, valuation and a command
   from our imperative language. If two such tuples are related, it means that if we are given
   a program state matching the first tuple, a valid single step of execution of our programming language 
   will give us back a new step, matching the second tuple. *)
(* One important advantage this kind of modeling has over interpreters is that this is a relation,
   as opposed to a function (in the case of interpreters). This means that a single program state may
   be related to several next-step states, which helps model things like non-determinism, randomized algorithms,
   concurrency, and parallelism. *)
Inductive step : heap * valuation * cmd -> heap * valuation * cmd -> Prop :=
(* Assign a value to a variable gives us a new valuation with the new value of the variable *)
(* Notice the use of Skip as the command in the next step. This indicates that this assignment
   statement has been consumed completely. Do not worry about sequencing or composing commands together
   other rules here will acheive that *)
| StAssign : forall h v x e,
  step (h, v, AssignVar x e) (h, v $+ (x, eval e h v), Skip)
(* AssignMem does not change the valuation, but it changes the heap *)
| StWrite : forall h v e1 e2,
  step (h, v, AssignMem e1 e2) (h $+ (eval e1 h v, eval e2 h v), v, Skip)

(* Sequencing base case: if we have sequence (c1; c2) and c1 is skip,
   then we can immediately go to c2. *)
| StStepSkip : forall h v c,
  step (h, v, Seq Skip c) (h, v, c)
(* Sequencing recursive case: if we have sequence (c1; c2) and c1 gets us to c1'
   then we can go to (c1'; c2), and any effects c1 had on heap and valuation are carried through. *)
| StStepRec : forall h1 v1 c1 h2 v2 c1' c2,
  step (h1, v1, c1) (h2, v2, c1')
  -> step (h1, v1, Seq c1 c2) (h2, v2, Seq c1' c2)

(* If statement execution depends on the value of its condition *)
| StIfTrue : forall h v b c1 c2,
  beval b h v = true
  -> step (h, v, If_ b c1 c2) (h, v, c1)
| StIfFalse : forall h v b c1 c2,
  beval b h v = false
  -> step (h, v, If_ b c1 c2) (h, v, c2)

(* While loop also depends on the value of its condition *)
| StWhileFalse : forall I h v b c,
  beval b h v = false
  -> step (h, v, While_ I b c) (h, v, Skip)
| StWhileTrue : forall I h v b c,
  beval b h v = true
  (* This is sometimes called loop unwinding, a loop with a true condition
     is equivalent to executing the body once, then going back to the loop *)
  -> step (h, v, While_ I b c) (h, v, Seq c (While_ I b c))

(* Finally, asserts have no effect, and are equivalent to skips *)
| StAssert : forall h v (a : assertion),
  a h v -> step (h, v, Assert a) (h, v, Skip).





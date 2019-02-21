Require Import Frap.

(*
 *
 * Modeling a small toy Imperative programming language to allow us to reason about it in Coq 
 *
 *)


(* 
 * 1: Our imperative language constructs and syntax.
 *)

(* natural number expression *)
Inductive natExp :=
| Const (n : nat)
| Var (x : string)
| Plus (e1 e2 : natExp).

Inductive cmd := (* Our commands *)
| Assign (x : var) (e : natExp)  (* Assign the value of e to variable x *)
| Seq (c1 c2 : cmd) (* sequence commands: c1 then c2 *)
| Repeat (n : nat) (body : cmd) (* Repeat a *FIXED* number of times *)
| Return (e1 : natExp). (* Return answer *)

(* BEGIN syntax macros that won't be explained *)
(* These allow us to override Coq's syntax with our own *)
Coercion Const : nat >-> natExp.
Coercion Var : string >-> natExp.
Infix "+" := Plus : cmd_scope.
Definition set (dst src : natExp) : cmd :=
  match dst with
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'repeat' n 'loop' body 'done'" := (Repeat n body) (at level 75).
Notation "'return' e" := (Return e) (at level 75).
Delimit Scope cmd_scope with cmd.
Infix "+" := plus : reset_scope.
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

(* our simple RAM: maps variables to their values *)
Definition valuation := fmap var nat.

(* Given a natural number expression and a valuation giving each variable a value
   This function describes the meaning of the expression by actually evaluating it *)
Fixpoint eval_nat_exp (e: natExp) (v: valuation): nat :=
  match e with
  | Const n => n
  | Var x => (v $! x) (* gets x from v, or returns 0 if x is not in v *)
  | Plus e1 e2 => (eval_nat_exp e1 v) + (eval_nat_exp e2 v)
  end.

(* One way to define semantics: using an interpreter *)
(* This task is a bit complicated because Gallina does not allow infinite execution
   In particular, it enforces that every recursive function must consume
   one of its parameters in decreasing order. *)
(* This is the main reason why in our language, we use Repeat <n> as opposed to a general
   While/for loop, and why we force <n> to be a constant number as opposed to a variable in our language. *)
(* We will define our interpreter in two parts: one for all statements except repeat, and the other
   just for repeat. Note that the way this is set up does not support nested repeats, but does
   support sequences of repeats. *)

(* No repeat interpreter: assume no repeat statement exists within c *)
Fixpoint no_repeat_interpret (c: cmd) (v: valuation): valuation :=
  match c with
  | Assign x e => v $+ (x, eval_nat_exp e v)
  | Seq c1 c2 => no_repeat_interpret c2 (no_repeat_interpret c1 v)
  | Return e => v $+ ("ret_", eval_nat_exp e v)
  | Repeat _ _ => v
  end.

(* Only repeat interpreter, (repeat_interpreter n c v) is used to interpret
   a (Repeat n c) statement with initial valuation v. It is assumed that c
   has no repeats inside it *)
Fixpoint repeat_interpreter (n: nat) (c: cmd) (v: valuation): valuation :=
  match n with
  | 0 => v
  | S n' => no_repeat_interpret c (repeat_interpreter n' c v)
  end.

(* Mix the two to form a generic interpreter *)
(* To support nest repeats, we could have merged the no_repeat_interpret and this function
   so that no_repeat_interpret can check and execute repeats. However, due to How gallina
   checks for termination, we would have had to use mutually recursive functions, more on this later *)
Fixpoint interpret' (c: cmd) (v: valuation): valuation :=
  match c with 
  | Repeat n c => repeat_interpreter n c v
  | Seq c1 c2 => interpret' c2 (interpret' c1 v)
  | _ => no_repeat_interpret c v
  end.

(* Top level interpreter for an entire program.
   Basically starts interpreting the program with an empty valuation
   and returns the result returned by the program *)
Definition interpret (c: cmd): nat :=
  (interpret' c $0) $! "ret_".



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
| Plus (e1 e2 : natExp)
| Minus (e1 e2: natExp)
| Times (e1 e2: natExp)
| FunctionCall (params: list string) (body: natExp) (args: list natExp).

(* BEGIN syntax macros that won't be explained *)
(* These allow us to override Coq's syntax with our own *)
(*
Coercion Const : nat >-> natExp.
Coercion Var : string >-> natExp.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Times : cmd_scope.
Notation "'_call_' f l " := (FunctionCall f l) (at level 75).
Notation "'_func_' l b" := (Def l b) (at level 70).
Delimit Scope cmd_scope with cmd.
Infix "+" := plus : reset_scope.
Infix "-" := minus : reset_scope.
Infix "*" := mult : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.
*)

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

(* Creates a new valuation representing the scope of a function call
   basically assigns the given arguments to the corresponding parameters *)
Fixpoint createScope (args: list nat) (parameters: list string): valuation :=
  match args with
  | nil => $0
  | cons n args' =>
      match parameters with
      | nil => $0
      | cons p params' => (createScope args' params') $+ (p, n)
      end
  end.

(* Given a natural number expression and a valuation giving each variable a value
   This function describes the meaning of the expression by actually evaluating it *)
Fixpoint eval_nat_exp (e: natExp) (v: valuation): nat :=
  match e with
  | Const n => n
  | Var x => (v $! x) (* gets x from v, or returns 0 if x is not in v *)
  | Plus e1 e2 => (eval_nat_exp e1 v) + (eval_nat_exp e2 v)
  | Minus e1 e2 => (eval_nat_exp e1 v) - (eval_nat_exp e2 v)
  | Times e1 e2 => (eval_nat_exp e1 v) * (eval_nat_exp e2 v)
  | FunctionCall params e args =>
      let
        fix eval_args (args: list natExp): list nat :=
          match args with
          | nil => nil
          | cons e a' => cons (eval_nat_exp e v) (eval_args a')
          end
      in
        eval_nat_exp e (createScope (eval_args args) params)
  end.

Definition interpret (e: natExp): nat :=
  eval_nat_exp e $0.


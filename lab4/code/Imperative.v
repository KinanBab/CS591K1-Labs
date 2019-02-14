Require Import Frap.

(* Modeling an (almost) full-feature Imperative programming language to allow us to reason about imperative programs in Coq 
 * Credits: Adam Chlipala - FRAP https://github.com/achlipala/frap
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
| Times (e1 e2 : exp).

(* Those were the expressions of numeric type.  Here are the Boolean
 * expressions. *)
Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

(* Modeling of memory *)
Definition heap := fmap nat nat.
Definition valuation := fmap var nat.
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
Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | ReadMem e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Times e1 e2 => eval e1 h v * eval e2 h v
  end.
Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
end.

(* Small-Step Operational semantics: https://en.wikipedia.org/wiki/Operational_semantics
   More on the difference between small and big step semantics:
   https://cs.stackexchange.com/questions/43294/difference-between-small-and-big-step-operational-semantics
*)
Inductive step : heap * valuation * cmd -> heap * valuation * cmd -> Prop :=
| StAssign : forall h v x e,
  step (h, v, AssignVar x e) (h, v $+ (x, eval e h v), Skip)

| StWrite : forall h v e1 e2,
  step (h, v, AssignMem e1 e2) (h $+ (eval e1 h v, eval e2 h v), v, Skip)

| StStepSkip : forall h v c,
  step (h, v, Seq Skip c) (h, v, c)

| StStepRec : forall h1 v1 c1 h2 v2 c1' c2,
  step (h1, v1, c1) (h2, v2, c1')
  -> step (h1, v1, Seq c1 c2) (h2, v2, Seq c1' c2)

| StIfTrue : forall h v b c1 c2,
  beval b h v = true
  -> step (h, v, If_ b c1 c2) (h, v, c1)
| StIfFalse : forall h v b c1 c2,
  beval b h v = false
  -> step (h, v, If_ b c1 c2) (h, v, c2)

| StWhileFalse : forall I h v b c,
  beval b h v = false
  -> step (h, v, While_ I b c) (h, v, Skip)
| StWhileTrue : forall I h v b c,
  beval b h v = true
  -> step (h, v, While_ I b c) (h, v, Seq c (While_ I b c))

| StAssert : forall h v (a : assertion),
  a h v -> step (h, v, Assert a) (h, v, Skip).

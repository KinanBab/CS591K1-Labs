Require Import Frap.
Require Import List.

Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| IntDiv (e1 e2 : exp)
| ArrRead (arr : list nat) (index: exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (be : bexp) (body : cmd)
| Return_ (e1 : exp).


(* BEGIN syntax macros that won't be explained *)
Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "e1 @[ e2 ]" := (ArrRead e1 e2) (no associativity, at level 70) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "/" := IntDiv : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'if_' b 'then' then_ 'else' else_ 'done'" := (If_ b then_ else_) (at level 75, b at level 0).
Notation "'while' b 'loop' body 'done'" := (While_ b body) (at level 75).
Notation "'return' e" := (Return_ e) (at level 75).
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.
(* END macros *)


Definition iterative_binary_search (arr: list nat) (n: nat) : cmd := (
  "lo" <- 0;;
  "hi" <- length(arr) ;;
  while "lo" < "hi" loop
    "mid" <- "lo" / "hi";;
    if_ arr @["mid"] = n then
      return 1
    else 
      if_ arr @["mid"] < n then
        "lo" <- "mid"
      else
        "hi" <- "mid"
      done
    done
  done ;;
  return 0
) % cmd.


(* TODO create a valuation as a map from string to nats.
   Create Fixpoint function to evaluate expression and bexp.
   Create small step semantics, and hoare logic, copy correctness proof.

   Move iterative_binary_search to binary_search.v
   create a file for modeling of arrays (as opposed to lists) and define sorted property
   Correcntessn theorem: behavior of iterative_binary_search should match
   recurisve binary search. *)
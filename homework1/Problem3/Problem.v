Require Import Modeling.

(* A useless transformation just to get you started
   Expands a given expression by adding 0 + <subexpression> for
   every subexpression in the expression.
   Example: (1 + 2) * x ===> 0 + ((0 + (0 + 1) + (0 + 2)) * x)
   clearly adding a bunch of zeros should have no effect.
*)
Fixpoint uselessTransformation (e: natExp): natExp :=
  match e with
  | Plus e1 e2 =>
      let e1' := uselessTransformation e1 in
      let e2' := uselessTransformation e2 in
        Plus (Const 0) (Plus e1' e2')
  | Minus e1 e2 =>
      let e1' := uselessTransformation e1 in
      let e2' := uselessTransformation e2 in
        Plus (Const 0) (Minus e1' e2')
  | Times e1 e2 =>
      let e1' := uselessTransformation e1 in
      let e2' := uselessTransformation e2 in
        Plus (Const 0) (Times e1' e2')
  | FunctionCall p e a => FunctionCall p (uselessTransformation e) a
  | _ => Plus (Const 0) e
  end.

(* More interesting transformation:
   This pre-evaluates any constant portion of the expression at ``compile''/transform time.
   So that the resulting expression is more optimized.
   Example: (1 + 2) * y => 3 * y
*)
Fixpoint constantsReducer (e: natExp): natExp :=
  match e with
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Minus (Const n1) (Const n2) => Const (n1 - n2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)

  | Plus e1 e2 => Plus (constantsReducer e1) (constantsReducer e2)
  | Minus e1 e2 => Minus (constantsReducer e1) (constantsReducer e2)
  | Times e1 e2 => Times (constantsReducer e1) (constantsReducer e2)

  | FunctionCall p e a => FunctionCall p (constantsReducer e) a
  | _ => e
  end.

Module Type Problem3.
  (* Here is something to get you going: prove that the useless transformation has no effect
     on any given expression and valuation.
     Notice that the definition of natExp in Modeling.v uses an inductive type.
     It is ideal to prove properties about such type using induction (look at lab 2).
     Use induction on the expression, you will get several goals, one for each constructor.
     Most are trivial, but here is a few hints:
     * for Plus and Minus, linear_arithmetic will help you reason about the effects of adding zero.
     * for Times, linear_arithmetic may or may not work depending on how you simplify and rewrite your terms
       consider using ring or equality instead. This is because Times is interepreted as a multiplication between
       two terms which is not linear.
     * Pay attention to the last case: FunctionCall. the actual goal is pretty easy to understand, the only
       difficulty is that the valuations are changed from the initial one. *)
  Axiom useless_is_uselsss: forall (e: natExp) (v: valuation),
    eval_nat_exp e v = eval_nat_exp (uselessTransformation e) v.

  (* Use what you learned from the previous part to prove this part. *)
  Axiom constants_reducer_correct: forall (e: natExp) (v: valuation),
    eval_nat_exp e v = eval_nat_exp (constantsReducer e) v.
End Problem3.

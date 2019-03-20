import .lambda

-- Problem 2: Lambda Calculus and Church Numerals (30 points for full credit, >=45 possible points with bonus)

-- From nat to Church Numerals
@[simp] def zero := term.abs 1 (term.abs 0 (term.var 0)) -- λf. λx. x

@[simp] def succ :=
  term.abs 2 
    (term.abs 1
      (term.abs 0
        (term.app 
          (term.var 1)
          (term.app
            (term.app (term.var 2) (term.var 1) )
            (term.var 0)
          )
        )
      )
    ) -- λn. λf. λx. [f]( [ [n](f) ] (x)  )

-- From nat to Church Numerals
@[simp] def from_nat' : nat -> term
| 0 := term.var 0
| (nat.succ n') := term.app (term.var 1) (from_nat' n')

@[simp] def from_nat : nat -> term
| n := (term.abs 1 (term.abs 0 (from_nat' n)))

-- From Church Numerals to nat
@[simp] def to_nat : term -> nat
| (term.var x) := 0
| (term.abs x t') := to_nat t'
| (term.app t t') := 1 + to_nat t'

-- Part A: Correctness of representation (5 points)
theorem repr_correct (n: nat) : to_nat (from_nat n) = n :=
begin
  -- #check nat.add_one
  -- Proof goes here
  induction n,
  simp,

  simp,
  rewrite nat.add_one,
  simp,
  assumption,
end

-- Part B: Correctness of zero (5 points)
theorem zero_correct : (from_nat 0) = zero :=
begin
  simp,
end

-- Part C: Correctness of successor (20 points)

-- Start by proving this helpful lemma, substituting a variable with
-- itself is useless.
lemma sub_useless (n: nat) (t: term) :
  (substitute (term.var n) n t) = t :=
begin
  -- use cases H: (<expression)
  -- to perform case analysis on expression while storing the case in Hypothesis H
  -- Proof goes here
  induction t,
    simp, cases H: (to_bool (t = n)),
      simp,
      simp,
      simp at H,
      apply eq.symm,
      assumption,

    simp, cases H: (to_bool (t_a = n)),
      simp, assumption,
      simp,

    simp, apply and.intro,
      assumption, assumption,
end

-- The main theorem
-- The proof will basically be repeated application of the correct constructor
--  either beta.app or beta.appl, or beta.appr, or beta.abs
--  depending on the form of the expression
-- THIS IS HIGHLY AUTOMATABLE, if you can automate it to any extent, you will get bonus points
--  proportional to how automated your solution is.
theorem succ_correct (n: nat) :
  (term.app succ (from_nat n)) l↠β (from_nat (nat.succ n)) :=
begin
  -- You can use these facts without proof
  -- Rewrite with the corresponding fact if you
  -- ever have something like ite (to_bool (<number> = <number>))
  -- inside your expressions (after dsimp or simp with a substitute)
  have H02: (to_bool (0 = 2) = ff), admit,
  have H12: (to_bool (1 = 2) = ff), admit,

  simp,
  constructor, -- rStar.trans
  apply beta.app,

  dsimp,
  rewrite H12,
  rewrite H02,
  simp,

  constructor, -- rStar.trans
  constructor, -- beta.abs
  constructor, -- beta.abs
  apply beta.appr,
  apply beta.appl,
  apply beta.app,
    
  constructor, -- rStar.trans
  constructor, -- beta.abs
  constructor, -- beta.abs
  apply beta.appr,
  apply beta.app,

  rewrite sub_useless,
  rewrite sub_useless,
  constructor, -- rStar.base
end


-- Bonus: Predecessor (15 points)
-- Encode and prove that predecessor is correct, you may ignore the case where the number is zero
-- Find its definitnion here: https://en.wikipedia.org/wiki/Church_encoding

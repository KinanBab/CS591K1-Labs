import .lambda
import .lemmas

-- silly lemmas
-- type of the identity
lemma identity_type :
  ∀ {t}, typing list.nil (λ:"x"."x") (type.func t t) :=
begin
  intros,
  apply typing.abs,
  apply typing.var,
  simp,  
end

-- type of the identity nested inside a silly abstraction
lemma nested_identity_type :
  ∀ {t}, typing list.nil (λ:"y".[λ:"x"."x"]("y")) (type.func t t) :=
begin
  intros,
  constructor,
  constructor,
     constructor,
     constructor,
     simp,

     constructor,
     simp,
end

-- type of the identity applied to anything
lemma free_var_type :
 ∀{t}, typing (list.cons ("y", t) list.nil) ([λ:"x"."x"]("y")) t :=
begin
  intros,
  constructor,
    constructor,
    constructor,
    simp,

    constructor,
    simp,
end


-- Type soundness
-- Type preservation (subject-reduction) + Progress = Type Soundness
-- page 6 at https://www.dropbox.com/s/1qnfsredovimvuq/lecture_slides_03.pdf?dl=0

-- Type preservation on →β
lemma type_preservation' (term1 term2: term):
  (term1 →β term2)
  → ∀{E t}, typing E term1 t -> typing E term2 t :=
begin
  intro,
  -- induction on term1 →β term2
  induction a,
    -- Application on the left
    intros,
    cases a,
    constructor,
    apply a_ih,
    assumption,
    assumption,

    -- Application on the right
    intros,
    cases a,
    constructor,
    assumption,
    apply a_ih,
    assumption,

    -- Application
    intros,
    cases a,
    cases a_a,
    apply type_preservation_substitute; assumption,
end

-- Full type preservation on ↠β
lemma type_preservation (term1 term2: term):
  (term1 ↠β term2)
  → ∀{E t}, typing E term1 t → typing E term2 t :=
begin
  intro,
  -- induction on term1 ↠β term2
  induction a; intros,
    -- trivial base (reflexive) case
    assumption,

    -- transitive case
    apply a_ih,
    apply type_preservation'; assumption,
end

-- Progress: a CLOSED typed lambda expression is either a value or can be evaluated
lemma progress (tr: term):
  ∀{t: type},
    typing list.nil tr t
    -> (value tr) ∨ (∃{tr2}, tr →β tr2) :=
begin
  induction tr; intros,
    -- variable
    left, constructor,

    -- abstraction
    left, constructor,

    -- application
    right,
    cases a,
    have H := tr_ih_a a_a,
    cases H,
      -- either left is a value or it can be evaluated
      -- value case
      cases H,
        -- either a var or an abstraction
        -- var case: there is a contradiction: a var cannot be typed to a function
        -- with an empty environment
        cases a_a,
        simp at a_a_a,
        exfalso,
        assumption,

        -- abstraction case
        existsi _,
        apply beta.app,

      -- left can be evaluated
      -- this means our expression can be evaluated by evaluating the left!
      cases H,
      existsi _,
      apply beta.appl,
      assumption,
end

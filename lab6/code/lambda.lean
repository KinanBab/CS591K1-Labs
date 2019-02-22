-- Syntax
inductive term
| var  : string  → term
| abs  : string → term → term
| app  : term → term → term

-- Custom notation
instance : has_coe string term := ⟨term.var⟩
notation `λ:`x `.` t := term.abs x t
notation `[`t1`](`t2`)` := term.app t1 t2

-- Substitution: the core of beta reduction
@[simp] def substitute : term -> string -> term -> term
| t v (term.var x) :=
    if to_bool (x = v) then t else (term.var x)
| t v (term.abs x t') :=
    if to_bool (x = v) then (term.abs x t') else (term.abs x (substitute t v t'))
| t v (term.app t1 t2) :=
    term.app (substitute t v t1) (substitute t v t2)

-- reflexive transative closure
inductive rStar {T} (rel: T -> T -> Prop) : T -> T -> Prop
| base : ∀ {t}, rStar t t
| trans {t1 t2 t3} : rel t1 t2 -> rStar t2 t3 -> rStar t1 t3

-- beta reduction
inductive beta : term -> term -> Prop
| appl: ∀{t1 t1' t2: term},
       beta t1 t1'
       -> beta (term.app t1 t2) (term.app t1' t2) 
| appr: ∀{t1 t2 t2': term},
       beta t2 t2'
       -> beta (term.app t1 t2) (term.app t1 t2')
| app :∀{x: string}, ∀{t1 t2: term},
       beta (term.app (term.abs x t1) t2) (substitute t2 x t1)

notation t `→β`:45 t' := beta t t'
notation t `↠β`:45 t' := (rStar beta) t t'

-- What is a normal form?
inductive normal_form : term -> Prop
| var: ∀{x}, normal_form (term.var x)
| abs: ∀{x t}, normal_form (term.abs x t)

-- Our simple types
inductive type
| dot  -- dot or constant type
| func: type -> type -> type -- function type: has domain and range types

-- Our typing rules
def env := list (string × type)
instance : has_append env := ⟨list.append⟩
@[simp] def type_from_env : env -> string -> type -> type
| list.nil v default := default
| (list.cons (x, t) env') v default :=
  if to_bool (v = x) then t else type_from_env env' v default

inductive typing : env -> term -> type -> Prop
| var: ∀{E x t},
       (type_from_env E x type.dot) = t
       -> typing E (term.var x) t
| abs: ∀{E x t1 b t2},
       typing (list.cons (x, t1) E) b t2
       -> typing E (term.abs x b) (type.func t1 t2)
| app: ∀{E term1 t1 term2 t2}, 
       typing E term1 (type.func t1 t2)
       -> typing E term2 t1
       -> typing E (term.app term1 term2) t2
            

-- silly lemmas
lemma identity_type :
  ∀ {t}, typing list.nil (λ:"x"."x") (type.func t t) :=
begin
  intros,
  apply typing.abs,
  apply typing.var,
  simp,  
end

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
lemma substitute1 (term x1 x2 t1 t2) :
      ∀{type}, to_bool (x1 = x2) = ff ->
      ∀{E1 E2: env}, typing (E1 ++ (x1, t1) :: (x2, t2) :: E2) term type -> typing (E1 ++ (x2, t2) :: (x1, t1) :: E2) term type :=
begin
  induction term; intros,
    constructor,
    cases a_1,
    induction E1,
      dsimp at *,
      cases H1: to_bool(term = x2); cases H2: to_bool (term = x1); rewrite H1 at *; rewrite H2 at *; simp at *,
        assumption, assumption, assumption,
        have H3: x1 = term, apply eq.symm H2,
        have H4: x1 = x2, apply eq.trans H3 H1,
        contradiction,

      cases E1_hd,
      dsimp at *,
      cases to_bool(term = E1_hd_fst),
        simp at *,
        apply E1_ih, assumption,

        simp at *,
        assumption,
      

    cases a_1,
    cases a_1,
    constructor,
    have H: (((term_a, a_1_t1) :: (E1 ++ (x2, t2) :: (x1, t1) :: E2)) = ((term_a, a_1_t1) :: E1) ++ (x2, t2) :: (x1, t1) :: E2), simp,
    rewrite H,
    apply term_ih, assumption, assumption,

    cases a_1,
    constructor,
      apply term_ih_a, assumption, assumption,

      apply term_ih_a_1, assumption, assumption,
end

lemma substitute2 (term x1 x2 t1 t2 type E) :
      to_bool (x1 = x2) = ff ->
      typing ((x1, t1) :: (x2, t2) :: E) term type -> 
      typing ((x2, t2) :: (x1, t1) :: E) term type :=
begin
  intro,
  have H: ((x1, t1) :: (x2, t2) :: E) = list.nil ++ ((x1, t1) :: (x2, t2) :: E), intros, simp,
  have H1: ((x2, t2) :: (x1, t1) :: E) = list.nil ++ ((x2, t2) :: (x1, t1) :: E), intros, simp,
  rewrite H, rewrite H1,
  apply substitute1,
  assumption,
end

lemma substitute3 (term) :
      ∀{type E1 E2 x1 t1 t2}, typing (E1 ++ (x1, t1) :: (x1, t2) :: E2) term type ->
      typing (E1 ++ (x1, t1) :: E2) term type :=
begin
  induction term; intros,
    cases a,
    constructor,
    induction E1,
      simp at *,
      cases (to_bool(term = x1)),
        simp at *,
        assumption,
        simp at *,
        assumption,

      cases E1_hd,
      simp at *,
      cases (to_bool(term = E1_hd_fst)); simp at *,
        apply E1_ih, assumption,
        assumption,

    cases a,
    constructor,
    have H: (((term_a, a_t1) :: (E1 ++ (x1, t1) :: E2)) = ((term_a, a_t1) :: E1) ++ (x1, t1) :: E2), simp,
    rewrite H,
    apply term_ih,
    assumption,

    cases a,
    constructor,
      apply term_ih_a, assumption,
      apply term_ih_a_1, assumption,
end

lemma substitute4 (term x1 t1 t2 E type) :
      typing ((x1, t1) :: (x1, t2) :: E) term type -> typing ((x1, t1) :: E) term type :=
begin
  have H: ((x1, t1) :: (x1, t2) :: E) = list.nil ++ ((x1, t1) :: (x1, t2) :: E), intros, simp,
  have H2: ((x1, t1) :: E) = list.nil ++ ((x1, t1) :: E), intros, simp,
  rewrite H, rewrite H2,
  apply substitute3,
end

lemma type_preservation_substitute (smallTerm bigTerm: term) (x: string) (smallType: type):
      ∀{E},
      typing E smallTerm smallType
      -> ∀{bigType}, typing (list.cons (x, smallType) E) bigTerm bigType
                      -> typing E (substitute smallTerm x bigTerm) bigType :=
begin
  induction bigTerm; intros,
    simp,
    cases a_1,
    dsimp at *,
    cases (to_bool(bigTerm = x)),
      simp at *,
      constructor,
      assumption,

      simp at *,
      rewrite <- a_1_a,
      assumption,
    
    cases a_1,
    cases a_1,
    simp,
    cases H: (to_bool(bigTerm_a = x)),
      simp,
      constructor,
      apply bigTerm_ih,
        admit,

        apply substitute2,
        assumption, assumption, 

      simp,
      constructor,
      simp at H,
      rewrite H at *,
      apply substitute4,
      assumption,

    intros,
    cases a_1,
    constructor,
      apply bigTerm_ih_a, assumption, assumption,
      apply bigTerm_ih_a_1, assumption, assumption,
end

lemma type_preservation' (term1 term2: term):
  (term1 →β term2)
  → ∀{E t}, typing E term1 t -> typing E term2 t :=
begin
  intro,
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
    apply type_preservation_substitute,
      assumption, assumption,
end

lemma type_preservation (term1 term2: term):
  (term1 ↠β term2)
  → ∀{E t}, typing E term1 t → typing E term2 t :=
begin
  intro,
  induction a,
    intros, assumption,

    intros,
    apply a_ih,
    apply type_preservation',
    assumption,
    assumption,
end

lemma progress (tr: term):
  ∀{t}, typing list.nil tr t -> (normal_form tr) ∨ (∃{tr2}, tr →β tr2) :=
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
    clear tr_ih_a tr_ih_a_1,
    cases H,
      cases H,
        cases a_a,
        simp at a_a_a,
        exfalso,
        assumption,

        existsi _,
        apply beta.app,

      cases H,
      existsi _,
      apply beta.appl,
      assumption,
end

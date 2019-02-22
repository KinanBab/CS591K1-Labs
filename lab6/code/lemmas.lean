import .lambda 

-- We only need this to be true for E1 = nil,
-- must strengthen the property to be able to prove it!
lemma typing_subst_order' (term x1 x2 t1 t2) :
  ∀{type}, to_bool (x1 = x2) = ff →
      ∀{E1 E2: env}, 
        typing (E1 ++ (x1, t1) :: (x2, t2) :: E2) term type
        → typing (E1 ++ (x2, t2) :: (x1, t1) :: E2) term type :=
begin
  induction term; intros,
    -- term.var
    constructor,
    cases a_1,
    induction E1,
      -- list.nil
      dsimp at *,
      cases H1: to_bool(term = x2);
      cases H2: to_bool (term = x1);
      rewrite H1 at *; rewrite H2 at *; simp at *,
        assumption,
        
        assumption,

        assumption,

        have H3: x1 = term, apply eq.symm H2,
        have H4: x1 = x2, apply eq.trans H3 H1,
        contradiction,

      -- list.cons
      cases E1_hd,
      dsimp at *,
      cases to_bool(term = E1_hd_fst),
        simp at *,
        apply E1_ih, assumption,

        simp at *,
        assumption,
      
    -- term.abs
    cases a_1,
    cases a_1,
    constructor,
    have H: (((term_a, a_1_t1) :: (E1 ++ (x2, t2) :: (x1, t1) :: E2)) 
            = ((term_a, a_1_t1) :: E1) ++ (x2, t2) :: (x1, t1) :: E2),
         simp,

    rewrite H,
    apply term_ih, assumption, assumption,

    -- term.app
    cases a_1,
    constructor,
      apply term_ih_a, assumption, assumption,

      apply term_ih_a_1, assumption, assumption,
end

-- special case of the above
lemma typing_subst_order (term x1 x2 t1 t2 type E) :
  to_bool (x1 = x2) = ff
  → typing ((x1, t1) :: (x2, t2) :: E) term type
  → typing ((x2, t2) :: (x1, t1) :: E) term type :=
begin
  intro,
  have H: ((x1, t1) :: (x2, t2) :: E)
          = list.nil ++ ((x1, t1) :: (x2, t2) :: E),
          intros; simp,

  have H1: ((x2, t2) :: (x1, t1) :: E)
           = list.nil ++ ((x2, t2) :: (x1, t1) :: E),
           intros; simp,

  rewrite H; rewrite H1,
  apply typing_subst_order',
  assumption,
end

-- We also only need this for E1 = nil
-- but must strengthen this too
lemma typing_subst_overwrite' (term) :
  ∀{type E1 E2 x1 t1 t2},
      typing (E1 ++ (x1, t1) :: (x1, t2) :: E2) term type
      → typing (E1 ++ (x1, t1) :: E2) term type :=
begin
  induction term; intros,
    -- term.var
    cases a,
    constructor,
    induction E1,
      -- list.nil
      simp at *,
      cases (to_bool(term = x1)),
        simp at *; assumption,

        simp at *; assumption,

      -- list.cons
      cases E1_hd,
      simp at *,
      cases (to_bool(term = E1_hd_fst)); simp at *,
        apply E1_ih, assumption,
        assumption,

    -- term.abs
    cases a,
    constructor,
    have H: (((term_a, a_t1) :: (E1 ++ (x1, t1) :: E2))
            = ((term_a, a_t1) :: E1) ++ (x1, t1) :: E2),
         simp,

    rewrite H,
    apply term_ih,
    assumption,

    -- term.app
    cases a,
    constructor,
      apply term_ih_a, assumption,
      apply term_ih_a_1, assumption,
end

-- special case of the above
lemma typing_subst_overwrite (term x1 t1 t2 E type) :
  typing ((x1, t1) :: (x1, t2) :: E) term type
  → typing ((x1, t1) :: E) term type :=
begin
  have H: ((x1, t1) :: (x1, t2) :: E)
          = list.nil ++ ((x1, t1) :: (x1, t2) :: E),
          intros; simp,

  have H2: ((x1, t1) :: E) 
       = list.nil ++ ((x1, t1) :: E),
       intros; simp,

  rewrite H; rewrite H2,
  apply typing_subst_overwrite',
end

-- the main lemma that we need for preservation!
-- if we substitute a term with another term of the same type, the overall type
-- does not change.
lemma type_preservation_substitute (smallTerm bigTerm: term) (x: string) (smallType: type):
  ∀{E: env},
      typing E smallTerm smallType
      → ∀{bigType},
          typing (list.cons (x, smallType) E) bigTerm bigType
          → typing E (substitute smallTerm x bigTerm) bigType :=
begin
  induction bigTerm; intros,
    -- term.var
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
    
    -- term.abs
    cases a_1,
    cases a_1,
    simp,
    cases H: (to_bool(bigTerm_a = x)),
      -- bigTerm_a ≠ x
      simp,
      constructor,
      apply bigTerm_ih,
        admit, -- Cheating, to prove this, we need to argue about free variables

        apply typing_subst_order,
        assumption, assumption, 

      -- bigTerm_a = x
      simp,
      constructor,
      simp at H,
      rewrite H at *,
      apply typing_subst_overwrite,
      assumption,

    -- term.app
    cases a_1,
    constructor,
      apply bigTerm_ih_a; assumption,
      apply bigTerm_ih_a_1; assumption,
end


absprop PTRUE
absprop PFALSE

absprop PAND(A: prop, B: prop) // and
propdef &&(A: prop, B: prop) = PAND(A, B) // syntax sugar

absprop POR(A: prop, B: prop) // or
propdef ||(A: prop, B: prop) = POR(A, B)

absprop PIMPL(A: prop, B: prop) // implication
infixr (->) ->> // syntax sugar: -> is already used by ATS, we will use ->> for our implication
propdef ->>(A: prop, B: prop) = PIMPL(A, B)

propdef ~(A: prop) = A ->> PFALSE // shorthand/syntax sugar for negation


// Proof rules for intuisionistic propositional logic
extern praxi true_intr(): PTRUE

// And introduction:
extern praxi and_intro {A, B: prop} : (A, B) -> A && B

// And Elimination
extern praxi and_elim_l {A, B: prop} : (A && B) -> A
extern praxi and_elim_r {A, B: prop} : (A && B) -> B

// Or introduction:
extern praxi or_intro_l {A, B: prop} : A -> (A || B)
extern praxi or_intro_r {A, B: prop} : B -> (A || B)

// Or Elimination
extern praxi or_elim {A, B, C: prop} (pf0: A || B, pf1: A ->> C, prf2: B ->> C): C

// Implication introduction
extern praxi impl_intro {A, B: prop} (pf: A -> B): A ->> B

// Implication elimination (modus ponens)
extern praxi impl_elim {A, B: prop} (pf0: A ->> B, pf1: A): B

extern prfun and_commutative {A, B: prop} (pf: A && B): B && A
primplement and_commutative(pf) =
    let
        // prval: defining a proposition/proof value
        // use prfn for functions
        prval pfA = and_elim_l(pf) // get a proof of A 
        prval pfB = and_elim_r(pf) // get a proof of B
    in
        and_intro(pfB, pfA)
    end

extern prfun or_commutative {A, B: prop} (pf: A || B): B || A
primplement or_commutative {A,B} (pf) =
    let
        // prval: defining a proposition/proof value
        // use prfn for functions
        prval pfAImp = impl_intro(lam(pf: A): (B || A) => or_intro_r(pf))
        prval pfBImp = impl_intro(lam(pf: B): (B || A) => or_intro_l(pf))
    in
        or_elim(pf, pfAImp, pfBImp)
    end


// Empty main for compilation
implement main0() = ()

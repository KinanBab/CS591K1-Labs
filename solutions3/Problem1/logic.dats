(*
 * Problem 1: Theorem proving using statics in ATS [45 points]
 *
 * The following is an encoding/modeling of the proof rules of intuisionistic propositional logic.
 * All proof rules from slide 8 from https://www.dropbox.com/s/9zz8eg0mq2apd84/lecture_slides_02.pdf 
 * are encoded for you below.
 *
 * However, false elimination (or exfalso) is not encoded!.
 *
 * Here is what you need to do:
 * Part A: [10 points] Encode false elemination: you can find it
 *    in slide 9 https://www.dropbox.com/s/9zz8eg0mq2apd84/lecture_slides_02.pdf)
 * Part B: [5 points] Prove that A -> ~A -> FALSE
 * Part C: [10 points] Prove that A ->> A is a tautology (is always true without assumptions)
 * Part D: [20 points] Formulate and prove associativity of OR
 *)



// absprop: Abstract Proposition: we are defining to static propositions named PTRUE and PFALSE
// these are just names, ATS does not really understand that they refer to true and false.
// We will teach ATS how to deal with them using the encoded rules below.
absprop PTRUE
absprop PFALSE



// Syntax of propositional logic
absprop PAND(A: prop, B: prop) // and
propdef &&(A: prop, B: prop) = PAND(A, B) // syntax sugar

absprop POR(A: prop, B: prop) // or
propdef ||(A: prop, B: prop) = POR(A, B)

absprop PIMPL(A: prop, B: prop) // implication
infixr (->) ->> // syntax sugar: -> is already used by ATS, we will use ->> for our implication
propdef ->>(A: prop, B: prop) = PIMPL(A, B)

propdef ~(A: prop) = A ->> PFALSE // shorthand/syntax sugar for negation


// Proof rules for intuisionistic propositional logic

// praxi: propositional axiom, this is similar to a function that takes some assumptions as paramters, and returns
//        the conclusion as a return value. These are axioms, they are not checked by the type checker nor are they
//        *implemented* in a concrete way.
extern praxi true_intr(): PTRUE  // Truth introduction: you can always introduce true without any assumptions

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



// Example on how to use the rules
// Proof that And is commutative
// Given a parameter (assumption) proving A && B, we must obtain a proof
//   of B && A using the proof rules above

// IMPORTANT:
// prfun: define the header of a proposition/proof function
// primplement: implemented a pre-defined header of a prfun
// prfn: allows you to define and implement at the same time
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

// End of provided code




// Start of solutions

// Part A: encode false elemination (exfalso):
// implementation goes here


// Part B: prove the following statements:
// prove that having A, ~A gives us a proof of PFALSE
extern prfun neg_elim {A: prop} (pf0: A, pf1: ~A): PFALSE

primplement neg_elim(pf0, pf1) =
  // implementation goes here


// Part C: prove that A ->> A
// Hint: think of the curry-howard isomorphism, this statement
//       is equivalent to the identity function!
prfn tauto {A: prop} (): A ->> A =
    // implementation goes here


// Part D: formulate and prove the associativity of or, namely
// that (X || Y) || Z and X || (Y || Z) are equivalent / the same



// Empty main for compilation
implement main0() = ()

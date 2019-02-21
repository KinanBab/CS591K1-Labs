Require Import Frap Modeling Helpers.

(* We use fib_loop_body to simplify how certain proof terms look.
   This is just a name that we are giving for this sub-program *)
Definition fib_loop_body: cmd := (
  "tmp" <- "cur" ;;
  "cur" <- "pre" + "cur";;
  "pre" <- "tmp"
) % cmd.

(* The fib iterative program in our language *)
Definition fib_iterative (n: nat) : cmd := (
    "pre" <- 0;;
    "cur" <- 1;;
    repeat n loop
      (* As if we copied-paste the content of the definition here *)
      fib_loop_body
    done ;;
    return "cur"
  ) % cmd.

(* The valuation we start the loop with *)
Definition loop_valuation: fmap var nat :=
  ($0 $+ ("pre", 0)) $+ ("cur", 1).


Module Type Problem2.
  (* You must implement a recursive version of fib using Gallina first *)
  Parameter fib: nat -> nat.

  (* These are helpful axioms/lemmas we suggest you start by proving.
     Each lemma will be useful in proving the subsequent lemma,
     If you are stuck proving anyone of these lemma, you can use
     the admit tactic to admit the current goal without proof, and the Admitted.
     command to end the proof. You can move on to prove other lemmas and using
     the lemma you have given up on in these proofs regularly. *)

  (* It is not required that you prove these lemmas or use them, they are 
     here just for guidance. For full credit, you only have to prove the
     last theorem 'fib_iterative_correct' in any way you wish *)


  (* This is very simple to prove, but is very powerful.
     We need to show that after the value of 'cur' at the end
     of an iteration, becomes the value of 'prev' at the next iteration.
     If you look at the definition of our program above, you will see it is
     very obvious. The proof will be obvious too. HINT: simplify to get a better
     understanding of what coq wants us to proof ;) *)
  Axiom fib_iterative_buildup: forall (n: nat) (v: valuation),
    repeat_interpreter (S n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "pre" =
    repeat_interpreter (n) fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur".

  (* The main bulk of the proof is here.
     We will focus only on what matters, and remove the useless parts of the code.
     All we want to show, is that if we interpret the repeat statement from our code
     n times, then the 'cur' variable will contain the fibonacci value at n *)
  (* Proving this is not hard, but relies on the following observation:
     The recursive implementation of Fibonacci makes two recursive calls (one for n-1 and one for n-2)
     The iterative implementation manipulates two variables, 'cur' and 'prev', at any iteration
     the first contains the value for n-1, and the second for n-2. *)
  (* Since this involves iteration, our best bet is to prove it by induction on n.
     You should try that out, and very quickly you will see that you can use the induction
     hypothesis to reason about the 'cur' and n-1, However, it will be very hard to reason
     about 'prev' and n-2, since the inductive hypothesis says nothing about them. *)
  (* To overcome this, we can use strong induction:
      https://math.stackexchange.com/questions/517440/whats-the-difference-between-simple-induction-and-strong-induction
     Strong induction provides a stronger induction hypothesis, one that applies for all m < n, as opposed
     to just n-1. Using that stronger hypothesis, and combining it with the previous lemma
     you will be able to reasons about 'prev' and n-2. *)
  (* Alternatively, you can choose to strengthen the inductive hypothesis, by proving another lemma first,
     one that states that for all n, 'prev' is equal to fib n and 'cur' is equal to fib n + 1 at the end
     of interpreting the repeat statement n times. *)

  (* HINT: we provide a tactic for using strong induction in Helpers.v called strong_induct,
           use it the same way you use induct. Helpers.v also contains our mathematical formulation
           of strong induction, and a Coq proof that it is a valid way of proving properties
           about natural numbers. *)
  Axiom fib_iterative_loop_correct: forall (n: nat) (v: valuation),
    repeat_interpreter n fib_loop_body (v $+ ("pre", 0) $+ ("cur", 1)) $! "cur" = fib n.

  (* If you proved the previous axiom/lemma, this will be very easy to use, just have
     Coq trim out the statements before and after the loop, and use the previous lemma.
     HINT: when you are stuck, simplify and unfold as much as you can. *)
  Axiom fib_iterative_correct': forall (n: nat) (v: valuation),
    (interpret' (fib_iterative n) v) $! "ret_" = fib n.

  (* This is the theorem you are required to prove. Notice that it is equivalent to the
     previous axiom/lemma, look at how interpret is defined in Modeling.v to believe it.
     If you proved the previous lemma, proving this will be also very simple.
     HINT: make sure Coq simplifies and unfolds interpret into its definition. *)
  Axiom fib_iterative_correct: forall (n: nat),
    interpret (fib_iterative n) = fib n.
End Problem2.

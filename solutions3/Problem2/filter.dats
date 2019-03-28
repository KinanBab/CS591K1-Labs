#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

(*
 * Problem 2: Certified/verified filter on list [25 points]
 * Part A: [10 points] filter with the most basic type signature, compile and double check it works!
 * Part B: [5 points] filter with a type-signature on the shape.
 * Part C: [10 points] incorrect filter satisfying the type signature: counter example!
 * Part D: bonus: [40 points] improve the typesignature!
 * 
 *)

// Part A: implement the given function
fun {A: t@ype} filter1 {n: nat} (f: A -> bool, l: list (A, n)): [m: nat] list(A, m) =
    case l of
    | list_nil() => list_nil()
    | list_cons(x, ls) =>
        if f(x)
            then list_cons(x, filter1(f, ls))
            else filter1(f, ls)

// Part B: implement the given function, make sure ATS type checks correctly
fun {A: t@ype} filter2 {n: nat} (f: A -> bool, l: list (A, n)): [m: nat | m <= n] list(A, m) =
    case l of
    | list_nil() => list_nil()
    | list_cons(x, ls) =>
        if f(x)
            then list_cons(x, filter2(f, ls))
            else filter2(f, ls)
    
// Part D: the previous type is clearly not enough for correctness
// implement a counter-example in ATS, a counter example
// is an implementation that ATS accepts (that compiles) but is not correct.
fun {A: t@ype} filter_incorrect {n: nat} (f: A -> bool, l: list (A, n)): [m: nat | m <= n] list(A, m) =
    list_nil()

fun {A: t@ype} filter_incorrect2 {n: nat} (f: A -> bool, l: list (A, n)): [m: nat | m <= n] list(A, m) =
    l

// Part C: bonus
// Can you improve the type signature even more?
// Think of an improvment that guarantees safety, similar to the one in Lean's homework.
// In other words, a statement that every element in the output list satisifies the filter function.
// Can you implement such type signature in ATS? Can you suggest any improvments or new features
// to ATS that would make this implementation possible or easier?
// HINT: the main difficulty is linking dynamics (the list and filter) to some statics, without having
// to reimplement everything at the static level!
// Partial solutions are fine, so are solutions written in english (in comments) or a mix or ATS and english!
// This is just food for thought!
// You will receive bonus credit proportional to how complete your solution is or how convincing your arguments are.
 
// Solution goes here



// Provided code for testing and running

// Printing the content of a list
fun print_list {m: int} (l: list(int, m)) =
    case l of
    | list_nil() => println!("")
    | list_cons(x, ls) =>
        print_list(ls) where {
            val () = print!(x, ", ")
        }

// main function
implement main0() = {
    fun f: int -> bool = lam(x) => x > 0
    val l: list(int, 5) = list_cons(~1, list_cons(1, list_cons(0, list_cons(~4, list_cons(5, list_nil())))))
    val () = print_list(filter1(f, l))
    val () = print_list(filter2(f, l))
    val () = print_list(filter_incorrect(f, l))
}

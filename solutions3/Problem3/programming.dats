#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

(*
 * Problem 3: Certified/verified programming [30 points]
 * Implement any two of the following, implement three or more for extra credits!
 * For full credits, your functions must use dependent types in their signature
 * to validate properties about the function. Properties about the shape of inputs/outputs
 * are fine, even if they do not imply full correctness.
 * The closer you are to full correctness, the more extra credit you will receive!
 * 
 * Part A: dot product: [15 points] a function that takes two lists of integers and
 *         returns an int representing their dot product
 *
 * Part B: left-partial sum: [15 points] a function that takes a list of integers, and
 *         returns a list containing the left-partial sum.
 *         example: [1, 0, -2, 4, 1] -> [1, 1, -1, 3, 4]
 *
 * Part C: even-odd: [25 points] a function that takes a nat as a parameter, and returns 
 *         true if it is even, otherwise odd.
 *   HINT: you will need to encode evenness and oddness as a static 
 *         inductive relation (inductive type ending with prop).
 *   HINT: look at this https://github.com/KinanBab/CS591K1-Labs/blob/master/lab7/2-fact/fact.dats 
 *         for inspiration.
 *
 * Part D: max: [40 points] a function that takes a list of nat as a parameter, and returns the max.
 *     TIP:  this is harder than the previous three exercises, keep it until the end.
 *     TIP2: you need to express what being a min of a list means in statics.
 *     TIP3: min can be defined inductively!
 *     TIP4: you can try to use list in statics as much as you would like, it wont work! maybe implement your own static version?
 *     TIP5: how different are your static specifications from your dynamic implementation? do you think this is an issue?
 *           can you think of ways to avoid this (either in ATS or the previous systems)?
 *           do you have suggestions to improve this in ATS?
 *)

// Part A
fun dot {n: nat} (l1: list(int, n), l2: list(int, n)): int =
    case(l1, l2) of
    | (list_nil(), list_nil()) => 0
    | (list_cons(x1, l1), list_cons(x2, l2)) => x1 * x2 + dot(l1, l2)

// Part B
fun partialsum {n: nat} (l: list(int, n)): list(int, n) =
let
    fun aux {m: nat | m <= n} (l: list(int, m), s: int): list(int, m) =
        case(l) of
        | list_nil() => list_nil()
        | list_cons(x, l) => list_cons(x + s, aux(l, x + s))
in
    aux(l, 0)
end

// Part C
dataprop EVEN(int, bool) =
| EVEN_ZERO (0, true)
| ODD_ONE (1, false)
| {n: int} {b: bool} EVEN_IND (n+1, ~b) of EVEN(n, b)

fun is_even {n: nat} (n: int(n)): [b: bool] (EVEN(n, b) | bool(b)) =
    if n = 0 then
        (EVEN_ZERO | true)
    else if n = 1 then
        (ODD_ONE | false)
    else
        let
            val (EVEN_REC | r) = is_even(n-1) where {
                prval () = $solver_assert(n > 1)
            }
        in
            (EVEN_IND(EVEN_REC) | ~r)
        end

// Part D
datasort intlist =
| snil
| scons of (int, intlist)

dataprop MAX(intlist, int) =
| MAX_NIL (snil(), 0)
| {l: intlist} {m: int} {x: int | m > x} MAX_CONS1 (scons(x, l), m) of (MAX(l, m))
| {l: intlist} {m: int} {x: int | m <= x} MAX_CONS2 (scons(x, l), x) of (MAX(l, m))

datatype dIntList (intlist) =
  | dnil(snil())
  | {a: int} {sl: intlist} dcons(scons(a, sl)) of (int(a), dIntList(sl))

fun max {l: intlist} (l: dIntList(l)): [r: int] (MAX(l, r) | int(r)) =
    case l of
    | dnil() => (MAX_NIL() | 0)
    | dcons(x, l) => let
        val (pf | m) = max(l)
      in
        if m > x
          then (MAX_CONS1(pf) | m)
          else (MAX_CONS2(pf) | x)
      end

// Some tests
implement main0() = {
    // call your functions on some inputs and print the results!
    val () = println!("Dot: ", dot( list_cons(5, list_cons(4, list_nil())), list_cons(~1, list_cons(2, list_nil()))   ))
    val () = println!("Partial Sum: ", partialsum( list_cons(5, list_cons(4, list_cons(~1, list_cons(2, list_nil()))))))

    val (_ | b) = is_even(102)
    val () = println!("Is Even: 102 = ", b)
    
    val (_ | m) = max(dcons(5, dcons(4, dcons(10, dcons(2, dnil())))))
    val () = println!("Max: ", m)
}




#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

// Dependent type function signatures!
fun abs (n: int): int =
  if n >= 0
    then n
    else ~n

fun abs2 {_n: int} (n: int(_n)): [r: int | r >= 0] int(r) =
  if n >= 0
    then n
    else ~n

fun abs3 {_n: int} (n: int(_n)): [r: int | r >= 0 && (r == _n || r == ~_n) ] int(r) =
  if n >= 0
    then n
    else ~n


sortdef nat = {a: int | a >= 0} 
fun abs4 {n: int} (n: int(n)): [r: nat | (r == n || r == ~n)] int(r) =
  if n >= 0
    then n
    else ~n



// Needs Z3 to compile
fun square {n: int} (n: int(n)): [r: nat | r == n*n] int(r) =
    n * n


// Main function, main0 is equivalent to void main()
implement main0 () =
  let
    val N = ~10
    val () = println! ("abs(", N, ") = ", abs(N))
    val () = println! ("abs2(", N, ") = ", abs2(N))
    val () = println! ("abs3(", N, ") = ", abs3(N))
    val () = println! ("abs4(", N, ") = ", abs4(N))
    val () = println! ("square(", N, ") = ", square(N))
  in
    ()
  end

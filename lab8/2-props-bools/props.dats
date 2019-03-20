#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

// http://ats-lang.sourceforge.net/EXAMPLE/EFFECTIVATS/PwTP-bool-vs-prop/main.html

// Implementation
fun fib_efficient (n: int) : int =
let
  fun loop (i: int, f0: int, f1: int) =
    if i+1 < n
      then loop (i+1, f1, f0+f1)
      else f1
in
  loop (0, 0, 1)
end


// Specification
dataprop FIB(int, int) =
| fib_base0(0, 0)
| fib_base1(1, 1)
| {n:nat}{r0,r1:int} fib_ind(n+2, r0+r1) of (FIB(n, r0), FIB(n+1, r1))


// Verified implementation
fun fib_verified {n: nat} (n: int(n)) : [r: int] (FIB(n ,r) | int(r)) =
let
  fun loop 
    {i: nat | i < n} {f0,f1: int} 
    (pf0: FIB(i, f0), pf1: FIB(i+1, f1) | i: int(i), f0: int(f0), f1: int(f1)): [r: int] (FIB(n, r) | int(r)) =
        if i+1 < n
          then loop(pf1, fib_ind(pf0, pf1) | i+1, f1, f0+f1)
          else (pf1 | f1)
in
  if n > 0 // bug was detected!
    then loop (fib_base0(), fib_base1() | 0, 0, 1)
    else (fib_base0() | 0)
end


implement main0() = {
  val () = println!("Fib(0) = ", fib_efficient(0)) // This is a bug
  val () = println!("Fib(1) = ", fib_efficient(1))
  val () = println!("Fib(2) = ", fib_efficient(2))
  val () = println!("Fib(3) = ", fib_efficient(3))
  val () = println!("Fib(4) = ", fib_efficient(4))
  val () = println!("Fib(5) = ", fib_efficient(5))
  val () = println!("Fib(10) = ", fib_efficient(10))
}


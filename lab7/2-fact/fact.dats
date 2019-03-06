#include  "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

// Specify FACT inductively
dataprop FACT_SPECS(int, int) =
| FACT_SPECS_BASE (0, 1)
| {n: nat} {r: nat} FACT_SPECS_BASE (n+1, (n+1)*r) of (FACT_SPECS(n, r))

// Simple Factorial function
fun fact1 {n: nat} (n: int(n)): [r: nat] (FACT_SPECS(n, r) | int(r)) =
  if n > 0
    then
      let
        val (prf | res) = fact1(n-1)
      in
        (FACT_SPECS_BASE(prf) | n * res)
      end
    else
      (FACT_SPECS_BASE | 1)

// Main
implement main0() = 
() where
{
  val N = 4
  val (_ | v) = fact1(N)
  val () = println! ("fact(", N, ") = ", v)
}

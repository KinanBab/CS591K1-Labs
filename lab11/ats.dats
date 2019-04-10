#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

fun even_even
{e1,e2,k1,k2: nat | e1 == 2*k1 && e2 == 2*k2}
(e1: int(e1), e2: int(e2)):
[r: nat | r == e1 + e2 && r == 2*(k1+k2)] int(r) =
    e1 + e2


fun odd_even
{o,e,k1,k2: nat | o == 2*k1+1 && e == 2*k2}
(o: int(o), e: int(e)):
[r: nat | r == o + e && r == 2*(k1+k2)+1] int(r) =
    o + e


implement main0() = {
    val () = println!("2 + 2 = ", even_even{2,2,1,1}(2, 2))
    val () = println!("2 + 3 = ", odd_even{3,2,1,1}(3, 2))
}



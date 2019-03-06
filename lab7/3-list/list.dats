#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

datatype mylist(t@ype, int) =
  | {a: t@ype} mynil(a, 0) // [of ()] is optional
  | {a: t@ype} {n:nat} mycons(a, n+1) of (a, mylist(a, n))

// not verified
fun {a: t@ype} mylength {n: int} (l: mylist(a, n)): int =
  case l of
    | mynil() => 0
    | mycons(_, l1) => 1 + mylength(l1)

// Better
fun {a: t@ype} mylength2 {n: int} (l: mylist(a, n)): int(n) =
  case l of
    | mynil() => 0
    | mycons(_, l1) => 1 + mylength2(l1)

// With termination
fun {a: t@ype} mylength3 {n: nat} .<n>. (l: mylist(a, n)): int(n) =
  case l of
    | mynil() => 0
    | mycons(_, l1) => 1 + mylength3(l1)


implement main0() = ()


#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

// Statics
datasort mylist_static =
 | snil
 | scons of (int, mylist_static)

// Specify FACT inductively
dataprop LIST_CONTAINS(int, mylist_static, bool) =
  | {a: int} LIST_CONTAINS_NIL (a, snil, false)
  | {a: int} {l: mylist_static} LIST_CONTAINS_TRUE (a, scons(a, l), true)

  | {a: int} {x: int | a != x} {l: mylist_static} {b: bool}
      LIST_CONTAINS_SAME (a, scons(x, l), b)
        of LIST_CONTAINS(a, l, b)

// Dynamics
datatype mylist_dynamic =
  | dnil
  | dcons of (int, mylist_dynamic)

// Encode list from statics
(*
dataprop related (mylist_static, mylist_dynamic) =
  | rnil(snil, dnil)
  | {a: int} {sl: mylist_static} {dl: mylist_dynamic}
      related(scons(a, sl), dcons(a, dl))
        of related(sl, dl)
*)

// Search
fun search {l: mylist_static}{a: int} (l: mylist_dynamic, a: int(a)): [b: bool] (LIST_CONTAINS(a, l, b) | bool(b)) =
  case l of
  | dnil => (LIST_CONTAINS_NIL() | false)
  | dcons(x, nl) =>
    if x = a
      then (LIST_CONTAINS_TRUE() | true)
      else (LIST_CONTAINS_SAME() | search(nl, x))

implement main0() = ()


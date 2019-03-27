#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"
#include "share/HATS/atspre_staload_libats_ML.hats"

// Statics
datasort sIntList =
 | snil of ()
 | scons of (int, sIntList)


// Specify what it means for a list to contain an element inductively
// this is an inductive relation, relating (a: int, l: sIntList, b: bool)
// such that l = true <-> a is in l
dataprop LIST_CONTAINS(int, sIntList, bool) =
  // snil: does not contain anything
  | {a: int} LIST_CONTAINS_NIL (a, snil, false)

  // scons: contains a if a is added by cons
  | {a: int} {l: sIntList} LIST_CONTAINS_TRUE (a, scons(a, l), true)

  // scons: if it adds a different element, result is unchanged
  | {a: int} {x: int | a != x} {l: sIntList} {b: bool}
      LIST_CONTAINS_SAME (a, scons(x, l), b) of LIST_CONTAINS(a, l, b)


// Dynamics: contains the length
// Notice how it links the statics and dynamics
datatype dIntList (int, sIntList) =
  // dnil matches snil and has length 0
  | dnil(0, snil())
  // constructs a list out of two parameters: a new int element a, and a previous (dynamic) list dl
  | {a: int} {n: nat} {sl: sIntList}
      dcons(n+1, scons(a, sl)) of (int(a), dIntList(n, sl))


// Search
fun search {l: sIntList}{a: int}{n: nat}(l: dIntList(n, l), a: int(a)):
  [b: bool] (LIST_CONTAINS(a, l, b) | bool(b)) =
    case l of
    | dnil() => (LIST_CONTAINS_NIL() | false)
    | dcons(x, nl) =>
      if x = a
        then (LIST_CONTAINS_TRUE() | true)
        else 
          let
            val (pf | b) = search(nl, a) // try replace a here by x and notice what happens
          in
            (LIST_CONTAINS_SAME(pf) | b)
          end

implement main0() = {
  val my_list = dcons(2, dcons(1, dcons(0, dnil()))) // Notice how at run-time, all the fancy types go away
  val (_ | res1) = search(my_list, 1)
  val (_ | res2) = search(my_list, 5)
  val () = println!("Search result is ", res1)
  val () = println!("Another Search result is ", res2)
}



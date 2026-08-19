(*
   lists.dats — the list library, exercised.

   Everything below is implemented in ATS itself, in the compiler's
   prelude, rather than as a shim in the emitter.  That is the point: a
   library written in the language is a test of the language, and every
   one of these functions is a template over an element type it never
   inspects.
*)

implement main0 () = {
//
val xs = list_make_intrange (0, 5)
val () = println! ("xs           = ", xs)
val () = println! ("length       = ", list_length<int> (xs))
val () = println! ("reverse      = ", list_reverse<int> (xs))
val () = println! ("append       = ", list_append<int> (xs, xs))
val () = println! ("take 3       = ", list_take<int> (xs, 3))
val () = println! ("drop 3       = ", list_drop<int> (xs, 3))
val () = println! ("nth 2        = ", list_nth<int> (xs, 2))
val () = println! ("last         = ", list_last<int> (xs))
//
val () = println! ("map (*2)     = ", list_map_cloref<int><int> (xs, lam x => x * 2))
val () = println! ("filter odd   = ", list_filter_cloref<int> (xs, lam x => x mod 2 = 1))
val () = println! ("foldl (+)    = ", list_foldleft_cloref<int><int> (xs, 0, lam (acc, x) => acc + x))
val () = println! ("exists >3    = ", list_exists_cloref<int> (xs, lam x => x > 3))
val () = println! ("forall >=0   = ", list_forall_cloref<int> (xs, lam x => x >= 0))
//
val () = print! ("foreach      = ")
val () = list_foreach_cloref<int> (xs, lam x => print! (x, " "))
val () = println! ("")
//
val yss = list_make_intrange (0, 3)
val () = println! ("tabulate sq  = ", list_tabulate_cloref<int> (5, lam i => i * i))
val () = println! ("concat       = ", list_concat<int> (list0_cons (xs, list0_cons (yss, list0_nil ()))))
//
var taken: int
val rest = list_takeout_at<int> (xs, 2, taken)
val () = println! ("takeout 2    = ", taken, " rest ", rest)
//
val () = println! ("insert 9 @1  = ", list_insert_at<int> (xs, 1, 9))
val () = println! ("remove @1    = ", list_remove_at<int> (xs, 1))
//
val strs = list0_cons ("a", list0_cons ("b", list0_nil ()))
val () = println! ("strings      = ", strs)
val () = println! ("mapped       = ", list_map_cloref<string><int> (strs, lam s => string_length (s)))
//
}

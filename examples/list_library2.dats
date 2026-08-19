(*
   list_library2.dats — sorting, options, and pairing.

   The second half of the list library, and `option` alongside it.  All
   of it in ATS: a merge sort is an algorithm, not a primitive, and a
   compiler that cannot express one in its own source language is not
   finished.
*)

implement main0 () = {
//
val xs = list0_cons (5, list0_cons (3, list0_cons (9, list0_cons (1, list0_cons (7, list0_nil ())))))
val () = println! ("xs        = ", xs)
val () = println! ("sorted    = ", list_mergesort_cloref<int> (xs, lam (a, b) => a <= b))
val () = println! ("desc      = ", list_mergesort_cloref<int> (xs, lam (a, b) => a >= b))
val () = println! ("merge     = ", list_merge_cloref<int> (list_make_intrange (0, 4), list_make_intrange (2, 6), lam (a, b) => a <= b))
//
val () = println! ("min       = ", list_min_cloref<int> (xs, lam (a, b) => a <= b))
val () = println! ("max       = ", list_max_cloref<int> (xs, lam (a, b) => a <= b))
//
val () = println! ("zip       = ", list_zip_with_cloref<int><int><int> (list_make_intrange (0, 3), list_make_intrange (10, 13), lam (a, b) => a + b))
//
val found = list_find_cloref<int> (xs, lam x => x > 6)
val () = println! ("find >6   = ", option_unwrap_or<int> (found, ~1))
val missing = list_find_cloref<int> (xs, lam x => x > 99)
val () = println! ("find >99  = ", option_unwrap_or<int> (missing, ~1))
val () = println! ("is some   = ", option_is_some<int> (found))
val () = println! ("mapped    = ", option_unwrap_or<int> (option_map_cloref<int><int> (found, lam x => x * 100), 0))
//
val () = println! ("index 9   = ", list_index_cloref<int> (xs, lam x => x = 9))
//
}

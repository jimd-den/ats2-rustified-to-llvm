//
// Strings, joined and cut.
//
// An ATS string is a run of bytes ending in a NUL that somebody else
// owns, so neither of these can write into what it was given: both ask
// the arena for room and copy. A substring is terminated where it was
// told to end rather than where the original did.
//
implement main0 () = {
  val hello = "hello"
  val world = "world"
  val () = println! ("append    = ", string_append (hello, ", "))
  val () = println! ("appended  = ", string_append (string_append (hello, ", "), world))
  val () = println! ("substring = ", string_make_substring (hello, 1, 3))
  val () = println! ("length    = ", string_length (string_append (hello, world)))
}

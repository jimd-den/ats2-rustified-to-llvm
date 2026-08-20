//
// The other half of ATS: not what a value is, but whose it is.
//
// A `datavtype` value is a *resource*. It must be consumed exactly
// once — used twice it is a use-after-free, never used it is a leak —
// and neither mistake is one an arithmetic solver would ever notice.
// `~mk_vt (x)` is the consuming match: it takes the box apart and the
// box is gone.
//
// `!b` is the other half of the discipline: lent, not given. `peek`
// may look inside and may not take the box away, and the caller still
// has it afterwards.
//
datavtype box_vt (a:t@ype) = mk_vt of (a)

fun peek (b: !box_vt(int)): int = case+ b of mk_vt (x) => x

fun unbox (b: box_vt(int)): int = case+ b of ~mk_vt (x) => x

fun sum_two (p: box_vt(int), q: box_vt(int)): int = unbox (p) + unbox (q)

implement main0 () = {
  val b = mk_vt (7)
  val () = println! ("peeked  = ", peek (b))
  val () = println! ("unboxed = ", unbox (b))
  val () = println! ("sum     = ", sum_two (mk_vt (20), mk_vt (22)))
}

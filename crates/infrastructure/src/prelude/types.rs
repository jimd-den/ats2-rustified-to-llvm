//! # Prelude Type & Constructor Canonicalization
//!
//! *Literate note.*  Maps ATS type aliases and standard type constructors to
//! their canonical representations in the compiler.

use ats2_domain::ast::Ty;

pub const PRELUDE_DATATYPES: &[&str] = &["list0", "stream_con", "option0"];

/// The runtime scalar behind an ATS primitive scalar spelling.
///
/// This compiler represents every integer as LLVM `i64` and every floating
/// value as LLVM `double`. The aliases need to be recognized centrally:
/// otherwise a bare signature parameter such as `(uint32)` or `(double)` is
/// mistaken for an untyped value name by the parser, while a directly built
/// AST may lower the same spelling as an opaque pointer.
pub fn canonical_scalar_type(name: &str) -> Option<&'static str> {
    match name {
        "int8" | "uint8" | "int16" | "uint16" | "int32" | "uint32" | "int64" | "uint64" => {
            Some("int")
        }
        "float" | "double" | "ldouble" => Some("double"),
        _ => None,
    }
}

/// Resolve a type name to the one the prelude actually declares, together
/// with how many of its arguments are *types* rather than static indices.
///
/// `list(int, n)` has two arguments but one type parameter: the `n` is a
/// length, which exists for the type checker and not at runtime.  Knowing
/// the declared arity is the only thing that can tell them apart, which is
/// why it is settled here rather than in the parser.
pub fn canonical_type(name: &str) -> Option<(&'static str, usize)> {
    match name {
        "list0" | "List0" | "list" | "List" | "list_vt" | "List0_vt" => Some(("list0", 1)),
        // A singly-linked list is the list this compiler already has:
        // the library that declares it differs in who owns the nodes,
        // which is a question of views and not of representation.
        "Sllist" | "sllist" | "sllist_vt" | "List1" | "list1" => Some(("list0", 1)),
        // `array`, `arrayptr` and `arrayref` differ in who owns the
        // cells and who may free them — views, all of it, and all erased
        // before anything runs.  One name here is what lets a function
        // declared over `&array(a, n)` be matched against an argument
        // whose type says `arrayptr(a)`.  The length is a static index,
        // so only the element type survives.
        "array" | "arrayptr" | "arrayref" | "arrszref" | "Array" | "Arrayptr" => Some(("array", 1)),
        // `bytes(n)` is `n` bytes; `b0ytes(n)` is `n` bytes nobody has
        // written yet.  The difference is a view, which this compiler
        // does not track.  There is no element type to name — bytes are
        // bytes — so every argument is a length.
        "bytes" | "b0ytes" | "bytes_v" | "b0ytes_v" => Some(("bytes", 0)),
        // `libats/ML/SATS/basis.sats` exports this alias to every ML unit.
        // A reference is represented by the pointer to its cell; the
        // `gvalue` element type governs source checking, not its LLVM shape.
        "gvref" => Some(("ptr", 0)),
        // ATS spells the option several ways, and the linear one differs
        // only in who may keep it.  `opt` is deliberately not among them:
        // it is a name a program is as likely to want for itself, and an
        // alias here would rename the program's own datatype out from
        // under it.
        "option" | "Option" | "option0" | "option_vt" | "Option_vt" => Some(("option0", 1)),
        // A linear stream differs from a lazy one in who may force it
        // and how often — a question for the type checker.  Both are a
        // thunk and the cell that remembers what it produced, so they
        // share a name here.
        "stream_con" | "stream_vt_con" | "lazy_con" => Some(("stream_con", 1)),
        _ => None,
    }
}

/// Expand a parameterized type alias supplied by the Postiats prelude.
///
/// These aliases are declared in distribution headers rather than in each
/// source unit that uses them. Keeping their expansion here gives the parser
/// the same ambient type vocabulary as the prelude declarations.
pub fn expand_type_alias(
    name: &str,
    args: &[ats2_domain::ast::Ty],
) -> Option<ats2_domain::ast::Ty> {
    use ats2_domain::ast::Ty;

    match (name, args) {
        ("fprint_type" | "emit_type", [value]) => Some(Ty::Fun(
            vec![Ty::Name("FILEref".into()), value.clone()],
            Box::new(Ty::Name("void".into())),
        )),
        ("jsonize_ftype", [value]) => Some(Ty::Fun(
            vec![value.clone()],
            Box::new(Ty::Name("jsonval".into())),
        )),
        _ => None,
    }
}

/// Whether a call hands its argument straight back, unchanged.
///
/// These are the casts and re-viewings ATS writes between types that
/// share one machine representation: `ptrcast` turns an `arrayptr` into
/// a `ptr`, `arrayptr_takeout` hands out the array inside one.  Each
/// moves no bits, and in ATS what it *does* move — which type the value
/// may now be read at — travels separately, in a proof.
///
/// Proofs are erased here, so a cast that inference could not see
/// through would take the element type with it and never give it back.
/// Treating these as transparent is what keeps `revarr (!p, n)` able to
/// say which instance it means, and it is honest: they are transparent
/// to the machine as well.
pub fn preserves_its_argument_type(name: &str) -> bool {
    matches!(
        name,
        "ptrcast"
            | "arrayptr2ptr"
            | "ptr2arrayptr"
            | "arrayptr_takeout"
            | "arrayptr_takeout_viewptr"
            | "arrayptr_refize"
            | "g0ofg1"
            | "g1ofg0"
            | "list_vt2t"
            | "list_t2vt"
            | "g0ofg1_list"
            | "unsafe_cast"
    )
}

/// Whether a type former names a suspended value — one that `!` forces.
///
/// ATS has four spellings for the same shape: lazy and linear, each with
/// its own word.  What separates them is who may force one and how
/// often, which is a question for the type checker.
pub fn is_a_suspension(name: &str) -> bool {
    matches!(name, "stream" | "stream_vt" | "lazy" | "llazy")
}

/// Whether a type former's first juxtaposed argument is a *type*.
///
/// ATS writes `stream N2` and `int n` the same way, and only the
/// former's declared sort says that one argument is a type and the
/// other a static index.  With no sort information to consult, the
/// formers whose argument is a type are listed — the list is short
/// because most of what a program juxtaposes really is an index.
pub fn takes_a_type_argument(name: &str) -> bool {
    matches!(
        name,
        "stream" | "stream_vt" | "lazy" | "llazy" | "stream_con" | "list0"
    )
}

/// Every constructor alias the prelude provides, as (alias, declared).
pub const CTOR_ALIASES: &[(&str, &str)] = &[
    ("nil", "list0_nil"),
    ("cons", "list0_cons"),
    ("list_nil", "list0_nil"),
    ("list_cons", "list0_cons"),
    ("nil0", "list0_nil"),
    ("nil_vt", "list0_nil"),
    ("cons_vt", "list0_cons"),
    ("list_vt_nil", "list0_nil"),
    ("list_vt_cons", "list0_cons"),
    ("cons0", "list0_cons"),
    ("list_vt_nil", "list0_nil"),
    ("list_vt_cons", "list0_cons"),
    ("None", "option0_none"),
    ("Some", "option0_some"),
    ("None_vt", "option0_none"),
    ("Some_vt", "option0_some"),
    ("option_none", "option0_none"),
    ("option_some", "option0_some"),
    ("stream_vt_nil", "stream_nil"),
    ("stream_vt_cons", "stream_cons"),
];

/// The constructor a prelude alias names.
///
/// `nil`/`cons` are the overloaded shorthands ATS programs actually write;
/// `list0_nil`/`list0_cons` are what the datatype declares.
pub fn canonical_ctor(name: &str) -> Option<&'static str> {
    match name {
        "nil" | "list_nil" | "nil0" | "list_vt_nil" | "nil_vt" => Some("list0_nil"),
        "cons" | "list_cons" | "cons0" | "list_vt_cons" | "cons_vt" => Some("list0_cons"),
        "None" | "None_vt" | "option_none" => Some("option0_none"),
        "Some" | "Some_vt" | "option_some" => Some("option0_some"),
        "stream_vt_nil" => Some("stream_nil"),
        "stream_vt_cons" => Some("stream_cons"),
        _ => None,
    }
}

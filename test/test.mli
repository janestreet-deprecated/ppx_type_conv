open Base

type t = int [@@deriving_inline sexp, compare]
val t_of_sexp : Sexplib.Sexp.t -> t
val sexp_of_t : t -> Sexplib.Sexp.t
val compare : t -> t -> int
[@@@end]

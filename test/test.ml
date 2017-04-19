open Base

type t = int [@@deriving_inline sexp, compare]
let t_of_sexp : Sexplib.Sexp.t -> t = int_of_sexp
let sexp_of_t : t -> Sexplib.Sexp.t = sexp_of_int
let compare : t -> t -> int = compare_int
[@@@end]

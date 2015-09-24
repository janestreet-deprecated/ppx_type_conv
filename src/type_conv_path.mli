open Parsetree
open Ppx_core.Std

class map : [string] Ast_traverse.map_with_context

val get_default_path     : Location.t -> string
val get_default_path_str : structure  -> string
val get_default_path_sig : signature  -> string

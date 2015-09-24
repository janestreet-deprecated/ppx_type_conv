open Parsetree
open Ppx_core.Std

val value_user : loc:Location.t -> expression -> structure_item

val add_dummy_user_for_values : Ast_traverse.map
val add_dummy_user_for_marked_values : Ast_traverse.map
val mark_values : Ast_traverse.map
val strip : Ast_traverse.map

open StdLabels
open Asttypes
open Parsetree
open Ppx_core.Std

[@@@metaloc loc]

let enter name path = if path = "" then name else path ^ "." ^ name

class map = object
  inherit [string] Ast_traverse.map_with_context as super

  method! structure_item_desc path x =
    match x with
    | Pstr_module mb -> super#structure_item_desc (enter mb.pmb_name.txt path) x
    | _ -> super#structure_item_desc path x

  method! module_declaration path md =
    super#module_declaration (enter md.pmd_name.txt path) md

  method! module_type_declaration path mtd =
    super#module_type_declaration (enter mtd.pmtd_name.txt path) mtd
end

let is_prefix ~prefix x =
  let prefix_len = String.length prefix in
  String.length x >= prefix_len && prefix = String.sub x ~pos:0 ~len:prefix_len
;;

let chop_prefix ~prefix x =
  if is_prefix ~prefix x then
    let prefix_len = String.length prefix in
    Some (String.sub x ~pos:prefix_len ~len:(String.length x - prefix_len))
  else
    None
;;

let get_default_path (loc : Location.t) =
  let fname = loc.loc_start.pos_fname in
  match chop_prefix ~prefix:"./" fname with
  | Some fname -> fname
  | None       -> fname
;;

let get_default_path_str = function
  | [] -> ""
  | { pstr_loc = loc; _ } :: _ -> get_default_path loc
;;

let get_default_path_sig = function
  | [] -> ""
  | { psig_loc = loc; _ } :: _ -> get_default_path loc
;;
